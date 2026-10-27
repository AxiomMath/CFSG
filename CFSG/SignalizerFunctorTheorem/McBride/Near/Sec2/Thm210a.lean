module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupGlobal

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

theorem thm210a
    (h : SemisimpleAction p A G) :
    IsDirectProduct {K | ∃ J ∈ lcal G, K = mOf A G ⊓ J} (mOf A G) ∧
      IsDirectProduct {K | ∃ J ∈ lcal G, K = kJ A J} (mOf A G) := by
  rw [h.mOf_eq_kProd]
  have hset : {K | ∃ J ∈ lcal G, K = kProd A G ⊓ J} = {K | ∃ J ∈ lcal G, K = kJ A J} := by
    ext K
    constructor
    · rintro ⟨J, hJ, rfl⟩
      exact ⟨J, hJ, h.kProd_inf hJ⟩
    · rintro ⟨J, hJ, rfl⟩
      exact ⟨J, hJ, (h.kProd_inf hJ).symm⟩
  rw [hset]
  exact ⟨h.isDirectProduct_kProd, h.isDirectProduct_kProd⟩

theorem thm210b
    (h : SemisimpleAction p A G) :
    IsGreatest {X : Subgroup Γ | X ≤ G ∧ cenIn G A ≤ X ∧ Group.IsSolvable X} (mOf A G) := by
  rw [h.mOf_eq_kProd]
  exact ⟨⟨kProd_le A G, h.cenIn_le_kProd, h.isSolvable_kProd⟩,
    fun X ⟨hXG, hD, hX⟩ => h.le_kProd_of_solvable hXG hD hX⟩

theorem thm210c
    (h : SemisimpleAction p A G) :
    IsMulCommutative (CFSG.fittingSubgroupOf (mOf A G)) ∧
      CFSG.fittingSubgroupOf (mOf A G) = cenIn G (CFSG.fittingSubgroupOf (cenIn G A)) := by
  rw [h.mOf_eq_kProd, h.fittingSubgroupOf_kProd]
  exact ⟨h.isMulCommutative_fProd,
    (h.cenIn_fittingSubgroupOf_eq (X := cenIn G A) inf_le_left le_rfl h.solvable_cen).symm⟩

theorem thm210e
    (h : SemisimpleAction p A G) {X : Subgroup Γ} (hXG : X ≤ G)
    (hX : Group.IsSolvable X) (hD : cenIn G A ≤ X) :
    mOf A G = norIn G (cenIn G (CFSG.fittingSubgroupOf X)) ∧ X ≤ mOf A G := by
  rw [h.cenIn_fittingSubgroupOf_eq hXG hD hX, h.norIn_fProd, h.mOf_eq_kProd]
  exact ⟨rfl, h.le_kProd_of_solvable hXG hD hX⟩

theorem thm210f
    (h : SemisimpleAction p A G) {X : Subgroup Γ} (hXG : X ≤ G)
    (hX : Admits (cenIn G A ⊔ A) X) (hnil : Group.IsNilpotent X) :
    X ≤ CFSG.fittingSubgroupOf (mOf A G) := by
  rw [h.mOf_eq_kProd, h.fittingSubgroupOf_kProd]
  refine h.le_fProd_of_nilpotent hXG hnil fun d hd y hy => ?_
  have hdN : d ∈ Subgroup.normalizer (X : Set Γ) := hX (Subgroup.mem_sup_left hd)
  exact (Subgroup.mem_normalizer_iff.mp hdN y).mp hy

end CFSG.SignalizerFunctorTheorem.McBride.Near
