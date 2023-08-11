use std::{
    collections::HashMap,
    env::current_dir,
    fs,
    io::Write,
    path::PathBuf,
    time::{Duration, Instant},
};
use bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
use core::{hint::black_box, marker::PhantomData};
use ff::PrimeField;
use nova_snark::{
    parallel_prover::{ParallelSNARK, NovaTreeNode},
    RecursiveSNARK,
    traits::{circuit::{StepCircuit, TrivialTestCircuit}, Group},
};
use num_bigint::BigInt;
use num_traits::Num;
use pasta_curves::{pallas::Point as G1, vesta::Point as G2, Fq};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

extern crate nova_snark;
extern crate custom_nova_scotia;
use custom_nova_scotia::{
    circom::{circuit::CircomCircuit, reader::{generate_witness_from_bin, generate_witness_from_wasm, load_r1cs}},
    create_parallel_public_params,
    create_recursive_circuit,
    FileLocation,
    F1, create_public_params,
};

// Type Aliases
type C1 = NonTrivialTestCircuit<<G1 as Group>::Scalar>;
type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

// Utility function to print the type of a value
fn print_type_of<T>(_: &T) {
    println!("{}", std::any::type_name::<T>());
}

// Struct representing the input file format
#[derive(Serialize, Deserialize)]
struct Inputfile {
    step_in: Vec<Vec<[String; 7]>>,
    pubkeys: Vec<Vec<[String; 7]>>,
    pubkeybits: Vec<u8>,
    signature: Vec<Vec<[String; 7]>>,
}

// Struct representing the Circom Input format
#[derive(Serialize, Deserialize)]
struct CircomInput {
    step_in: Vec<String>,
    #[serde(flatten)]
    extra: HashMap<String, Value>,
}

// Circuit definition for NonTrivialTestCircuit
#[derive(Clone, Debug, Default)]
struct NonTrivialTestCircuit<F: PrimeField> {
    num_cons: usize,
    _p: PhantomData<F>,
}

// Implementation for NonTrivialTestCircuit
impl<F> NonTrivialTestCircuit<F>
where
    F: PrimeField,
{
    pub fn new(num_cons: usize) -> Self {
        Self {
            num_cons,
            _p: Default::default(),
        }
    }
}

impl<F> StepCircuit<F> for NonTrivialTestCircuit<F>
where
    F: PrimeField,
{
    fn arity(&self) -> usize {
        1
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        // Consider an equation: `x^2 = y`, where `x` and `y` are respectively the input and output.
        let mut x = z[0].clone();
        let mut y = x.clone();
        for i in 0..self.num_cons {
            y = x.square(cs.namespace(|| format!("x_sq_{i}")))?;
            x = y.clone();
        }
        Ok(vec![y])
    }

    fn output(&self, z: &[F]) -> Vec<F> {
        let mut x = z[0];
        let mut y = x;
        for _i in 0..self.num_cons {
            y = x * x;
            x = y;
        }
        vec![y]
    }
}

//------------------------------------------------------
//------------------------------------------------------
fn binarytreeprover() {
    // Define paths for circuit and witness files
    let root = PathBuf::from("/");
    let circuit_file = root.join("src/novatest_aggregate_bls_verify_512.r1cs");
    let witness_generator_file = root.join("src/novatest_aggregate_bls_verify_512_cpp/novatest_aggregate_bls_verify_512");

    // Load the R1CS from the circuit file
    println!("Reading in R1CS...");
    let start = Instant::now();
    let r1cs = load_r1cs(&FileLocation::PathBuf(circuit_file));
    println!("R1CS readin took: {:?}", start.elapsed());

    // Generate Common Reference String (CRS)
    println!("Creating a CRS");
    let start = Instant::now();
    let pp = create_parallel_public_params(r1cs.clone()); //this setup required for ParallelSNARK
    //let pp = create_public_params(r1cs.clone()); //this setup required for RecursiveSNARK
    println!("CRS creation took {:?}", start.elapsed());

    // Print information about the CRS
    print_type_of(&pp);
    println!("the size of 'pp setup' is {}", std::mem::size_of_val(&pp));
    println!("Number of constraints per step (primary circuit): {}", pp.num_constraints().0);
    println!("Number of constraints per step (secondary circuit): {}", pp.num_constraints().1);
    println!("Number of variables per step (primary circuit): {}", pp.num_variables().0);
    println!("Number of variables per step (secondary circuit): {}", pp.num_variables().1);

    // Number of constraints in the step circuit
    let num_cons = pp.num_constraints().1;


    // Reading the input file
    let inputs: Inputfile = serde_json::from_str(include_str!("src/novainput_aggregate_bls_verify_512.json")).unwrap();

    // Convert public input data to the correct format
    let mut pubin = Vec::new();
    for x in 0..2 {
        for k in 0..7 {
            pubin.push(F1::from_str_vartime(&inputs.step_in[x][0][k]).unwrap());
        }
        for k in 0..7 {
            pubin.push(F1::from_str_vartime(&inputs.step_in[x][1][k]).unwrap());
        }
    }
    let start_public_input = pubin.clone();
    println!("public inputs are: {:?}", start_public_input);

    // Define lengths to iterate over
    let pubkeylen = inputs.pubkeys.len();
    let pubkeybitlen = inputs.pubkeybits.len();
    let signaturelen = inputs.signature.len();
   
    let mut iteration_count = 0;
    let mut j = 2;//number of starting committees

     // Main loop for recursiveSNARK creation and verification over each iteration
    for i in 1..=5 {
        let iteration_count = j; // Setting iteration count
        println!("iteration count {}", j);

        // Creating private inputs from a JSON source.
        // These are organized into hashmaps, which are then placed into a vector.
        let mut private_inputs = Vec::new();
        for _ in 0..iteration_count {
            let mut private_input = HashMap::new();
            private_input.insert("pubkeys".to_string(), json!(inputs.pubkeys[0..pubkeylen]));
            private_input.insert("pubkeybits".to_string(), json!(inputs.pubkeybits[0..pubkeybitlen]));
            private_input.insert("signature".to_string(), json!(inputs.signature[0..signaturelen]));
            private_inputs.push(private_input);
        }

        println!("this is the length of private inputs: {:?}", private_inputs.len());


        // Prepare for witness generation
        let witness_generator_output = root.join("circom_witness.wtns");
        let iteration_count = private_inputs.len();

        // Convert start_public_input to hexadecimal
        let start_public_input_hex = start_public_input
            .iter()
            .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
            .collect::<Vec<String>>();
        let mut current_public_input = start_public_input_hex.clone();

        // Set up the circuit's secondary attributes
        let circuit_secondary = TrivialTestCircuit::default();
        let z0_secondary = vec![<G2 as Group>::Scalar::zero()];
        let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;

        let decimal_stringified_input: Vec<String> = current_public_input
            .iter()
            .map(|x| BigInt::from_str_radix(x, 16).unwrap().to_str_radix(10))
            .collect();

        let input = CircomInput {
            step_in: decimal_stringified_input.clone(),
            extra: private_inputs[0].clone(),
        };

        let input_json = serde_json::to_string(&input).unwrap();
        let witgenfile = FileLocation::PathBuf(witness_generator_file.clone());

        // Generate witness from C++ bin
        let witness = generate_witness_from_bin::<<G1 as Group>::Scalar>(
            &witness_generator_file,
            &input_json,
            &witness_generator_output,
        );
        // Remove temporary witness file
        fs::remove_file(witness_generator_output);

        // Create circuit with r1cs and witness
        let circuit = CircomCircuit {
            r1cs: r1cs.clone(),
            witness: Some(witness),
        };



        //------------------------------------------
        // Binary tree construction using ParallelSNARK
        println!("Total number of steps to be proven: {:?}", iteration_count);
        println!("Creating a new ParallelSNARK instance...");

        let start = Instant::now();
        let mut prover = ParallelSNARK::new(
            &pp,
            iteration_count,
            start_public_input.clone(),
            z0_secondary.clone(),
            circuit.clone(),
            circuit_secondary.clone(),
        );

        println!("ParallelSNARK instantiation took {:?}", start.elapsed());
        

        // Generate proving tree
        println!("Generating proof for ParallelSNARK...");

        let start = Instant::now();
        let res = prover.prove(&pp, &circuit, &circuit_secondary);

        println!("ParallelSNARK proof creation took {:?}", start.elapsed());

        j*=2
    }

}

fn parallelforkprover() {
    // Define paths for circuit and witness files
    let root = PathBuf::from("/");
    let circuit_file = root.join("src/novatest_aggregate_bls_verify_512.r1cs");
    let witness_generator_file = root.join("src/novatest_aggregate_bls_verify_512_cpp/novatest_aggregate_bls_verify_512");

    // Load the R1CS from the circuit file
    println!("Reading in R1CS...");
    let start = Instant::now();
    let r1cs = load_r1cs(&FileLocation::PathBuf(circuit_file));
    println!("R1CS readin took: {:?}", start.elapsed());

    // Generate Common Reference String (CRS)
    println!("Creating a CRS");
    let start = Instant::now();
    let ppp = create_parallel_public_params(r1cs.clone()); //this setup required for ParallelSNARK
    let pp = create_public_params(r1cs.clone());
    println!("CRS creation took {:?}", start.elapsed());

    // Print information about the CRS
    print_type_of(&pp);
    println!("the size of 'pp setup' is {}", std::mem::size_of_val(&pp));
    println!("Number of constraints per step (primary circuit): {}", pp.num_constraints().0);
    println!("Number of constraints per step (secondary circuit): {}", pp.num_constraints().1);
    println!("Number of variables per step (primary circuit): {}", pp.num_variables().0);
    println!("Number of variables per step (secondary circuit): {}", pp.num_variables().1);

    // Number of constraints in the step circuit
    let num_cons = pp.num_constraints().1;

    // Reading the input file
    let inputs: Inputfile = serde_json::from_str(include_str!("src/novainput_aggregate_bls_verify_512.json")).unwrap();

    // Convert public input data to the correct format
    let mut pubin = Vec::new();
    for x in 0..2 {
        for k in 0..7 {
            pubin.push(F1::from_str_vartime(&inputs.step_in[x][0][k]).unwrap());
        }
        for k in 0..7 {
            pubin.push(F1::from_str_vartime(&inputs.step_in[x][1][k]).unwrap());
        }
    }
    let start_public_input = pubin.clone();
    println!("public inputs are: {:?}", start_public_input);

    // Define lengths to iterate over
    let pubkeylen = inputs.pubkeys.len();
    let pubkeybitlen = inputs.pubkeybits.len();
    let signaturelen = inputs.signature.len();

    let mut iteration_count = 2;//how many committees in the Nova chain

    for i in 1..=1 {
        // Define private inputs based on iteration counts
        let mut private_inputs = Vec::new();
        for y in 0..iteration_count {
            let mut private_input = HashMap::new();
            private_input.insert("pubkeys".to_string(), json!(inputs.pubkeys[0..pubkeylen]));
            private_input.insert("pubkeybits".to_string(), json!(inputs.pubkeybits[0..pubkeybitlen]));
            private_input.insert("signature".to_string(), json!(inputs.signature[0..signaturelen]));
            private_inputs.push(private_input);
        }

        let witness_generator_output = root.join("circom_witness.wtns");
        
        println!("this is the length of private inputs: {:?}", private_inputs.len());
        
        let start_public_input_hex = start_public_input
        .iter()
        .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
        .collect::<Vec<String>>();
        let mut current_public_input = start_public_input_hex.clone();

        let circuit_secondary = TrivialTestCircuit::default();
        let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

        let mut recursive_snark: Option<RecursiveSNARK<G1, G2, CircomCircuit<Fq>, C2>> = None;


        let decimal_stringified_input: Vec<String> = current_public_input
        .iter()
        .map(|x| BigInt::from_str_radix(x, 16).unwrap().to_str_radix(10))
        .collect();

        let input = CircomInput {
            step_in: decimal_stringified_input.clone(),
            extra: private_inputs[0].clone(),
        };

        let input_json = serde_json::to_string(&input).unwrap();

        // Generate witness from C++ bin
        let witness = generate_witness_from_bin::<<G1 as Group>::Scalar>(
            &witness_generator_file,
            &input_json,
            &witness_generator_output,
        );    

        let circuit = CircomCircuit {
            r1cs: r1cs.clone(),
            witness: Some(witness),
        };

                    
        // Creating a RecursiveSNARK using standard Nova
        println!("Creating a RecursiveSNARK...");
        let start = Instant::now();
        for i in 0..iteration_count {
            let current_public_output = circuit.get_public_outputs();
            current_public_input = current_public_output
                .iter()
                .map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string())
                .collect();
    
            let res = RecursiveSNARK::prove_step(
                &pp,
                recursive_snark,
                circuit.clone(),
                circuit_secondary.clone(),
                start_public_input.clone(),
                z0_secondary.clone(),
            );
            assert!(res.is_ok());
            recursive_snark = Some(res.unwrap());
        }
        fs::remove_file(witness_generator_output);
    
        let recursive_snark = recursive_snark.unwrap();

        //duplicate it to simulate a second running Nova instance of equal length

        let recursive_snark1 = recursive_snark.clone();

        println!("RecursiveSNARK creation took {:?}", start.elapsed());
        let prover_time = start.elapsed();



        // Verify the recursive snark
        println!("Verifying a RecursiveSNARK...");
        let start = Instant::now();
        let res = recursive_snark.verify(&pp, iteration_count, start_public_input.clone(), z0_secondary.clone());
        println!("RecursiveSNARK::verify: {:?}, took {:?}", res, start.elapsed());
        let verifier_time = start.elapsed();
        assert!(res.is_ok());


        let node1 = NovaTreeNode::convert(
            &ppp,
            recursive_snark,
            circuit.clone(),
            TrivialTestCircuit::default(),
            0 as u64,
            start_public_input.clone(),
            vec![<G1 as Group>::Scalar::zero()],
            z0_secondary.clone(),
            vec![<G2 as Group>::Scalar::zero()],
        );
        if node1.is_ok() {
            print!("Is okay");
        } else {
            print!{"Node convert not okay with error {:?}", node1.err().unwrap()};
        }
        //assert!(node2.is_ok());
 
        let node2 = NovaTreeNode::convert(
            &ppp,
            recursive_snark1,
            circuit.clone(),
            TrivialTestCircuit::default(),
            0 as u64,
            start_public_input.clone(),
            vec![<G1 as Group>::Scalar::zero()],
            z0_secondary.clone(),
            vec![<G2 as Group>::Scalar::zero()],
        );
        if node2.is_ok() {
            print!("Is okay");
        } else {
            print!{"Node convert not okay with error {:?}", node2.err().unwrap()};
        }
        //assert!(node2.is_ok());
        let node1_unwrapped = node1.unwrap();
        let node2_unwrapped = node2.unwrap();

        println!("Merging nodes...");
        let start = Instant::now();

        let res_2 = node1_unwrapped.merge(
            node2_unwrapped,
            &ppp,
            &circuit,
            &TrivialTestCircuit::default(),
        );
        if res_2.is_ok() {
            print!("Is okay");
        } else {
            print!{"Merge not okay with error {:?}", res_2.err().unwrap()};
        }
        //assert!(res_2.is_ok());

        println!("Node merge took: {:?}", start.elapsed());

    }



}

fn main() {

    binarytreeprover();
    //parallelforkprover();
}

