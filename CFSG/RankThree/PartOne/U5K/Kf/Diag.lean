module

public import CFSG.RankThree.PartOne.U5K.Hyp.Para

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}

theorem eq_of_mul_lmat_eq (x : Gam hK) {M N : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (h : M * lmat x = N * lmat x) : M = N := by
  have hinv : lmat x * (((x.1.left⁻¹ : GL (HypIndex 2 1) K)) : Matrix _ _ K) = 1 := by
    rw [lmat, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc M = M * lmat x * (((x.1.left⁻¹ : GL (HypIndex 2 1) K)) : Matrix _ _ K) := by
        rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = N * lmat x * (((x.1.left⁻¹ : GL (HypIndex 2 1) K)) : Matrix _ _ K) := by rw [h]
    _ = N := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]

theorem act_mem_Ssub_of_oddDiag (x : Gam hK) (hx : x.1.right = 1)
    {A : Matrix (Fin 2) (Fin 2) K} (hA : IsUnit A.det) {d : K} (hd : hK.bar d * d = 1)
    (hl : lmat x = oddDiag hK A d) {s : hypSU hK 2 1} (hs : s ∈ Ssub hK) :
    act hK x s ∈ Ssub hK := by
  obtain ⟨-, y, C, hsm⟩ := hs
  have hact := lmat_mul_map x s
  have hmap : (mat s).map x.1.right = mat s := by
    ext i j
    simp [hx]
  rw [hmap, hsm, hl, oddDiag_mul_oddUni_comm hK hA hd y C] at hact
  have heq := eq_of_mul_lmat_eq x (M := mat (act hK x s)) (N := oddUni hK (d⁻¹ • (A *ᵥ y))
    (A * C * (A.map hK.bar)ᵀ)) (by rw [hl]; exact hact.symm)
  exact mem_Ssub_of_mat heq

theorem Phi_mem_normalizer_Sh (x : Gam hK) (hx : x.1.right = 1)
    {A : Matrix (Fin 2) (Fin 2) K} (hA : IsUnit A.det) {d : K} (hd : hK.bar d * d = 1)
    (hl : lmat x = oddDiag hK A d) :
    Phi hK x ∈ Subgroup.normalizer (Sh hK : Set (MulAut (hypPSU hK 2 1))) := by
  have := finite_mulAut_hyp hK
  refine mem_normalizer_of_conj_le fun ρ hρ => ?_
  obtain ⟨s, hs, rfl⟩ := hρ
  refine ⟨act hK x s, act_mem_Ssub_of_oddDiag x hx hA hd hl hs, ?_⟩
  exact (Phi_mul_innM_mul_inv x s).symm

end CFSG.RankThree.PartOne.U5K.Kf
