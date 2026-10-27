module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L67
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L63
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L62b
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68.Claim
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68.Bot

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem lemma_6_8
    (h : Counterexample p A θ) :
    IsSimpleGroup (CFSG.inSubgroup CFSG.generalizedFitting (thetaOf θ A)) ∧
      ¬ IsMulCommutative (CFSG.inSubgroup CFSG.generalizedFitting (thetaOf θ A)) := by
  obtain ⟨J, hJ⟩ := L68.lcal_thetaOf_nonempty h
  obtain ⟨W, hW⟩ := L68.exists_isGreatest h hJ
  have hW0 : W = ⊥ := L68.eq_bot h hJ hW
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  have hC : thetaOf θ A ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc thetaOf θ A ⊓ Subgroup.centralizer (J : Set G)
        ≤ θ a ⊓ Subgroup.centralizer (J : Set G) := inf_le_inf_right _ (thetaOf_le_apply ha ha1)
      _ ≤ W := hW.apply_inf_le a ha ha1
      _ = ⊥ := hW0
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  rw [L68.inSubgroup_generalizedFitting_eq hJ hC]
  exact ⟨hs, hnc⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
