module

public import CFSG.Quasithin.Background.SmithB49Act
public import CFSG.Quasithin.Background.SmithB49Fox

public section

namespace CFSG.Quasithin.B5.B49

open Matrix CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5.Ln
open scoped Kronecker

@[expose] def relsN4 : Fin 7 → List (Fin 2) :=
  ![
    [0, 0],
    [1, 1, 1, 1],
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
    [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
      1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0]]

@[expose] def actN4 : Fin 2 → List ℕ :=
  ![
    [3, 2, 4, 8, 51, 34, 68, 136, 768, 512, 1024, 2048, 12288, 8192, 16384, 32768],
    [32768, 4096, 8192, 16384, 8, 1, 2, 4, 128, 16, 32, 64, 2048, 256, 512, 1024]]

@[expose] def certPN4 : Fin 2 → List ℕ :=
  ![
    [0, 1, 64, 128, 128, 17, 1, 64, 64, 256, 17, 1, 1, 4096, 128, 0],
    [1, 0, 0, 0, 16, 1, 64, 128, 384, 0, 1025, 2112, 2, 0, 8, 0]]

@[expose] def certCN4 : Fin 2 → Fin 7 → List ℕ :=
  ![
    ![
      [0, 1, 64, 128, 0, 17, 0, 0, 0, 256, 272, 1, 0, 4096, 384, 257],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 8, 2],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 17],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]],
    ![
      [0, 0, 64, 0, 0, 0, 0, 0, 0, 4288, 0, 0, 0, 64, 4288, 0],
      [0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 1],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 64, 0],
      [0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 0],
      [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]

theorem actN4_spec (i : Fin 2) :
    decM finProdFinEquiv (actN4 i) = (mats4inv i)ᵀ ⊗ₖ mats4 i := by
  fin_cases i <;> decide +kernel

theorem relsN4_spec : ∀ r, wordEvalB 4 mats4B (relsN4 r) = bone 4 := by
  decide +kernel

theorem certN4_bits : ∀ j l, certL (4 * 4) actN4 certPN4 (fun _ => []) (fun _ => []) j l =
    certR (4 * 4) actN4 relsN4 certCN4 j l := by
  decide +kernel

theorem h1N4 {c : ↥(StatedSL 4 (ZMod 2)) → (Fin 4 × Fin 4 → ZMod 2)}
    (hc : c ∈ Z1A (muK (matHom 4))) : c ∈ B1A (muK (matHom 4)) := by
  refine mem_B1A_of_cert closure_sgen4 (A := fun i => decM finProdFinEquiv (actN4 i))
    (fun i v => by rw [muK_apply, krM_sgen4_mat, actN4_spec])
    (rels := relsN4) (fun r => wordEval_sgen4_eq_one (relsN4_spec r))
    (fun l => decM finProdFinEquiv (certPN4 l)) (fun j r => decM finProdFinEquiv (certCN4 j r))
    (fun j l => ?_) hc
  have h := cert_of_bits finProdFinEquiv actN4 certPN4 (fun _ => []) (fun _ => []) relsN4
    certCN4 certN4_bits j l
  rwa [decM_nil, Matrix.zero_mul, add_zero] at h

end CFSG.Quasithin.B5.B49
