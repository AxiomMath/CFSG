module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Quot
public import CFSG.Quasithin.EmptyFaithful.S151S4D
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin.F146Field

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Case2a

variable {G : Type} [Group G]

structure Setting (T M H K : Subgroup G) : Prop where
  min : MinParabolic H T (H ⊓ M)
  comp : K ∈ cComp H
  sup : H = K ⊔ T
  norm : T ≤ Subgroup.normalizer (K : Set G)
  ker : ∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
    ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H

variable {T M H K : Subgroup G}

theorem Setting.le_H (c : Setting T M H K) : K ≤ H := le_of_mem_cComp c.comp

theorem Setting.sylow (c : Setting T M H K) : IsSylowTwoOf T H := c.min.isSylow

theorem Setting.le_inf (c : Setting T M H K) : T ≤ H ⊓ M :=
  (isUniqueMaxOver_iff.mp c.min.uniqueMax).2.1

theorem Setting.le_M (c : Setting T M H K) : T ≤ M := c.le_inf.trans inf_le_right

theorem Setting.le_H' (c : Setting T M H K) : T ≤ H := c.le_inf.trans inf_le_left

theorem Setting.H_le_normalizer (c : Setting T M H K) : H ≤ Subgroup.normalizer (K : Set G) := by
  rw [c.sup]
  exact sup_le Subgroup.le_normalizer c.norm

section Fin

variable [Finite G]

theorem Setting.oTwoUpper_eq (c : Setting T M H K) : oTwoUpper H = K := by
  have h := S151S4.twoResidual_sup_eq_self c.norm c.sylow.2.1 (perfect_of_mem_cComp c.comp)
  rw [← c.sup, F6.twoResidual_eq_oTwoUpper] at h
  exact h

theorem Setting.sylow_inf (c : Setting T M H K) : IsSylowTwoOf (T ⊓ K) K :=
  A4.isSylowTwoOf_inf_normal c.sylow c.le_H c.H_le_normalizer

theorem Setting.pCore_le_normalizer (c : Setting T M H K) :
    pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) :=
  P134.pCoreOf_le_normalizer_of_mem_cComp c.comp

theorem Setting.pCore_le (c : Setting T M H K) : pCoreOf 2 H ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf c.sylow

end Fin

theorem Setting.not_le_M (c : Setting T M H K) (hHM : ¬ H ≤ M) : ¬ K ≤ M := by
  intro h
  apply hHM
  rw [c.sup]
  exact sup_le h c.le_M

theorem Setting.cComp_mem (c : Setting T M H K) :
    K ∈ cComp (K ⊔ S1421.sOf T K) := by
  have h : S1421.sOf T K = T := inf_eq_left.mpr c.norm
  rw [h, ← c.sup]
  exact c.comp

end Case2a

end CFSG.Quasithin.F146Field
