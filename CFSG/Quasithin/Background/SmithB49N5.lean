module

public import CFSG.Quasithin.Background.SmithB49Act
public import CFSG.Quasithin.Background.SmithB49Fox

public section

namespace CFSG.Quasithin.B5.B49

open Matrix CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5.Ln
open scoped Kronecker

@[expose] def relsN5 : Fin 5 → List (Fin 2) :=
  ![
    [0, 0],
    [1, 1, 1, 1, 1],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1],
    [0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]]

@[expose] def actN5 : Fin 2 → List ℕ :=
  ![
    [3, 2, 4, 8, 16, 99, 66, 132, 264, 528, 3072, 2048, 4096, 8192, 16384, 98304, 65536, 131072,
      262144, 524288, 3145728, 2097152, 4194304, 8388608, 16777216],
    [16777216, 1048576, 2097152, 4194304, 8388608, 16, 1, 2, 4, 8, 512, 32, 64, 128, 256, 16384,
      1024, 2048, 4096, 8192, 524288, 32768, 65536, 131072, 262144]]

@[expose] def certPN5 : Fin 2 → List ℕ :=
  ![
    [0, 1, 128, 256, 512, 512, 33, 1, 128, 256, 256, 1024, 33, 1, 128, 128, 32768, 1024, 33, 1, 1,
      1048576, 256, 512, 0],
    [1, 0, 0, 0, 0, 32, 1, 128, 256, 512, 1536, 0, 4097, 8320, 16640, 49408, 0, 131072, 266241,
      532608, 2, 0, 8, 16, 0]]

@[expose] def certCN5 : Fin 2 → Fin 5 → List ℕ :=
  ![
    ![
      [0, 1, 128, 256, 512, 0, 33, 0, 0, 0, 0, 1024, 0, 1, 128, 0, 32768, 512, 33, 1, 0, 1048576,
        33152, 1024, 0],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 0, 0, 16, 1, 2, 0, 0, 8, 16, 1],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 4096, 524288, 0, 0, 512, 135201, 1, 0, 0, 524416,
        4194304, 135168],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 1]],
    ![
      [0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 34048, 0, 0, 0, 0, 1048960, 0, 0, 0, 0, 128, 1048960,
        34048, 0],
      [0, 0, 4, 0, 0, 0, 16, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 0, 17],
      [0, 0, 0, 0, 0, 0, 4194816, 0, 0, 0, 0, 32768, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 128, 32768,
        4194816],
      [0, 0, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1024, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17]]]

theorem actN5_spec (i : Fin 2) :
    decM finProdFinEquiv (actN5 i) = (mats5inv i)ᵀ ⊗ₖ mats5 i := by
  fin_cases i <;> decide +kernel

theorem relsN5_spec : ∀ r, wordEvalB 5 mats5B (relsN5 r) = bone 5 := by
  decide +kernel

theorem certN5_bits : ∀ j l, certL (5 * 5) actN5 certPN5 (fun _ => []) (fun _ => []) j l =
    certR (5 * 5) actN5 relsN5 certCN5 j l := by
  decide +kernel

theorem h1N5 {c : ↥(StatedSL 5 (ZMod 2)) → (Fin 5 × Fin 5 → ZMod 2)}
    (hc : c ∈ Z1A (muK (matHom 5))) : c ∈ B1A (muK (matHom 5)) := by
  refine mem_B1A_of_cert closure_sgen5 (A := fun i => decM finProdFinEquiv (actN5 i))
    (fun i v => by rw [muK_apply, krM_sgen5_mat, actN5_spec])
    (rels := relsN5) (fun r => wordEval_sgen5_eq_one (relsN5_spec r))
    (fun l => decM finProdFinEquiv (certPN5 l)) (fun j r => decM finProdFinEquiv (certCN5 j r))
    (fun j l => ?_) hc
  have h := cert_of_bits finProdFinEquiv actN5 certPN5 (fun _ => []) (fun _ => []) relsN5
    certCN5 certN5_bits j l
  rwa [decM_nil, Matrix.zero_mul, add_zero] at h

end CFSG.Quasithin.B5.B49
