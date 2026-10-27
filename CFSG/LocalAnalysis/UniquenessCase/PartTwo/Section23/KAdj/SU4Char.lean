module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SUOHinf
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniCuts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (flagStabilizer)
open CFSG.AGLEmbedding.LeviBlock (eBlockHom eIdx predCut coe_eBlockHom)

variable {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)

@[expose] noncomputable def su4Chi : ↥(flagStabilizer h 2 0 {2}) →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp
    ((eBlockHom h (Nat.zero_le 1) (I := {2}) (b := 2) (by simp) (by norm_num) le_rfl).comp
      (Subgroup.inclusion (le_of_eq (by rw [Finset.coe_singleton]))))

private lemma det_submatrix_eIdx_D03 (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (hM : M.BlockTriangular fullPos) :
    (M.submatrix (eIdx 2 0 (a := predCut ({2} : Finset ℕ) 2) (le_rfl : 2 ≤ 2))
        (eIdx 2 0 (a := predCut ({2} : Finset ℕ) 2) (le_rfl : 2 ≤ 2))).det =
      M (Sum.inl 0) (Sum.inl 0) * M (Sum.inl 1) (Sum.inl 1) := by
  let φ : Fin (2 - predCut ({2} : Finset ℕ) 2) → HypIndex 2 0 :=
    eIdx 2 0 (a := predCut ({2} : Finset ℕ) 2) (le_rfl : 2 ≤ 2)
  have hdet : (M.submatrix φ φ).det =
      (M.submatrix φ φ) (0 : Fin 2) (0 : Fin 2) * (M.submatrix φ φ) (1 : Fin 2) (1 : Fin 2) -
        (M.submatrix φ φ) (0 : Fin 2) (1 : Fin 2) * (M.submatrix φ φ) (1 : Fin 2) (0 : Fin 2) :=
    Matrix.det_fin_two (show Matrix (Fin 2) (Fin 2) K from M.submatrix φ φ)
  have h00 : (M.submatrix φ φ) (0 : Fin 2) (0 : Fin 2) = M (Sum.inl 0) (Sum.inl 0) := rfl
  have h11 : (M.submatrix φ φ) (1 : Fin 2) (1 : Fin 2) = M (Sum.inl 1) (Sum.inl 1) := rfl
  have h01 : (M.submatrix φ φ) (0 : Fin 2) (1 : Fin 2) = M (Sum.inl 0) (Sum.inl 1) := rfl
  have h10 : (M.submatrix φ φ) (1 : Fin 2) (0 : Fin 2) = 0 :=
    hM (show fullPos (Sum.inl 0) < fullPos (Sum.inl 1) from by decide)
  change (M.submatrix φ φ).det = M (Sum.inl 0) (Sum.inl 0) * M (Sum.inl 1) (Sum.inl 1)
  rw [hdet, h00, h11, h01, h10, mul_zero, sub_zero]

private lemma coe_su4Chi_eq_det_sub_D03 (g : ↥(flagStabilizer h 2 0 {2})) :
    ((su4Chi h g : Kˣ) : K) =
      ((((g : hypSU h 2 0) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K).submatrix
          (eIdx 2 0 (a := predCut ({2} : Finset ℕ) 2) (le_rfl : 2 ≤ 2))
          (eIdx 2 0 (a := predCut ({2} : Finset ℕ) 2) (le_rfl : 2 ≤ 2))).det := by
  unfold su4Chi
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply,
    coe_eBlockHom, Subgroup.coe_inclusion]

theorem coe_su4Chi_of_mem_hypBorel (g : ↥(flagStabilizer h 2 0 {2}))
    (hg : (g : hypSU h 2 0) ∈ hypBorel h 2 0) :
    ((su4Chi h g : Kˣ) : K) =
      (((g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
          (Sum.inl 0) (Sum.inl 0) *
        (((g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
          (Sum.inl 1) (Sum.inl 1) := by
  have htri := blockTriangular_of_mem_hypBorel h (Nat.zero_le 1) hg
  rw [coe_su4Chi_eq_det_sub_D03 h g]
  exact det_submatrix_eIdx_D03
    (((g : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) htri

theorem su4_diag_mul_eq_one_of_mem_hinf {g : ↥(hypSU h 2 0)}
    (hg : g ∈ Hinf (flagStabilizer h 2 0 {2})) (hB : g ∈ hypBorel h 2 0) :
    (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
          (Sum.inl 0) (Sum.inl 0)) *
        (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
          (Sum.inl 1) (Sum.inl 1)) = 1 := by
  obtain ⟨hQ, h1⟩ := suo_hom_eq_one_of_mem_hinf (su4Chi h) inferInstance hg
  have h2 := coe_su4Chi_of_mem_hypBorel h ⟨g, hQ⟩ hB
  rw [h1, Units.val_one] at h2
  exact h2.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
