module

public import CFSG.Quasithin.Background.SmithB49Act
public import CFSG.Quasithin.Background.SmithB49Fox

public section

namespace CFSG.Quasithin.B5.B49

open Matrix CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5.Ln
open scoped Kronecker

@[expose] def relsD5 : Fin 4 → List (Fin 2) :=
  ![
    [0, 0],
    [1, 1, 1, 1, 1],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1],
    [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
      1]]

@[expose] def actD5 : Fin 2 → List ℕ :=
  ![
    [99, 66, 132, 264, 528, 96, 64, 128, 256, 512, 3072, 2048, 4096, 8192, 16384, 98304, 65536,
      131072, 262144, 524288, 3145728, 2097152, 4194304, 8388608, 16777216],
    [16777216, 1048576, 2097152, 4194304, 8388608, 16, 1, 2, 4, 8, 512, 32, 64, 128, 256, 16384,
      1024, 2048, 4096, 8192, 524288, 32768, 65536, 131072, 262144]]

@[expose] def certPD5 : Fin 2 → List ℕ :=
  ![
    [2, 4, 1048576, 16, 7, 7, 2, 4, 8, 16, 16, 1024, 2, 4, 8, 8, 32768, 1024, 2, 4, 4, 1048576,
      16, 7, 2],
    [64, 128, 4, 512, 160, 128, 0, 0, 0, 0, 1024, 0, 4096, 8192, 16384, 49152, 0, 131072, 266240,
      532480, 130, 0, 520, 176, 65]]

@[expose] def certCD5 : Fin 2 → Fin 4 → List ℕ :=
  ![
    ![
      [0, 0, 0, 0, 0, 1028, 32, 4, 1048576, 16, 0, 1024, 0, 1028, 1048576, 0, 32768, 0, 32, 4, 0,
        1048576, 16, 1024, 32],
      [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 18, 4, 0, 0, 0, 1, 2, 0, 0, 8, 16, 1],
      [0, 0, 0, 0, 0, 4210691, 0, 0, 8, 0, 0, 0, 8192, 28675, 1048576, 0, 0, 4194304, 8192, 16384,
        0, 0, 16, 4194304, 2],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 524288, 0, 0, 0, 524288, 0, 0, 0, 0, 0, 0, 0]],
    ![
      [0, 0, 0, 0, 0, 0, 0, 0, 1081348, 0, 0, 33840, 0, 0, 0, 0, 1082368, 0, 0, 0, 0, 1081348,
        1082368, 33840, 0],
      [0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 25, 0, 0, 0, 0, 24, 0, 0, 0, 2, 14, 16, 9, 1],
      [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 4202504, 0, 0, 0, 0, 1032, 0, 0, 0, 0, 12, 1032, 4202504,
        0],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 524304, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 524304, 0]]]

theorem actD5_spec (i : Fin 2) :
    decM finProdFinEquiv (actD5 i) = mats5 i ⊗ₖ mats5 i := by
  fin_cases i <;> decide +kernel

theorem relsD5_spec : ∀ r, wordEvalB 5 mats5B (relsD5 r) = bone 5 := by
  decide +kernel

theorem certD5_bits : ∀ j l, certL (5 * 5) actD5 certPD5 (fun _ => []) (fun _ => []) j l =
    certR (5 * 5) actD5 relsD5 certCD5 j l := by
  decide +kernel

theorem h1D5 {c : ↥(StatedSL 5 (ZMod 2)) → (Fin 5 × Fin 5 → ZMod 2)}
    (hc : c ∈ Z1A (muK (dmatHom 5))) : c ∈ B1A (muK (dmatHom 5)) := by
  refine mem_B1A_of_cert closure_sgen5 (A := fun i => decM finProdFinEquiv (actD5 i))
    (fun i v => by rw [muK_apply, krM_sgen5_dmat, actD5_spec])
    (rels := relsD5) (fun r => wordEval_sgen5_eq_one (relsD5_spec r))
    (fun l => decM finProdFinEquiv (certPD5 l)) (fun j r => decM finProdFinEquiv (certCD5 j r))
    (fun j l => ?_) hc
  have h := cert_of_bits finProdFinEquiv actD5 certPD5 (fun _ => []) (fun _ => []) relsD5
    certCD5 certD5_bits j l
  rwa [decM_nil, Matrix.zero_mul, add_zero] at h

end CFSG.Quasithin.B5.B49
