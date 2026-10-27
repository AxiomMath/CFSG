module

public import CFSG.GroupTheory.LocalCores.Components
public import Mathlib.Algebra.Group.Commutator
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

theorem isComponentOf_mem_of_le_sSup {Y : Type*} [Group Y] [Finite Y] {C : Subgroup Y}
    {𝒟 : Set (Subgroup Y)} (hC : IsComponentOf C ⊤) (h𝒟 : ∀ D ∈ 𝒟, IsComponentOf D ⊤)
    (hle : C ≤ sSup 𝒟) : C ∈ 𝒟 := by
  classical
  by_contra hCnot
  have hCn : CFSG.IsComponent C :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native C).1 hC
  have hDn : ∀ D ∈ 𝒟, CFSG.IsComponent D := fun D hD =>
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native D).1 (h𝒟 D hD)
  have hcomm : ∀ D ∈ 𝒟, ⁅C, D⁆ = ⊥ := by
    intro D hD
    rcases CFSG.LocalCores.distinct_components_commute hCn (hDn D hD) with h | h
    · exact absurd (h.symm ▸ hD) hCnot
    · exact h
  have hDle : ∀ D ∈ 𝒟, D ≤ Subgroup.centralizer (C : Set Y) := by
    intro D hD
    have hDC : ⁅D, C⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hcomm D hD
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDC
  have hsSup : sSup 𝒟 ≤ Subgroup.centralizer (C : Set Y) := sSup_le hDle
  have hCle : C ≤ Subgroup.centralizer (C : Set Y) := hle.trans hsSup
  have hcommC : ⁅C, C⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hCle
  have hbot : C = ⊥ := by
    have hperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp hCn.1.1
    rw [hcommC] at hperf
    exact hperf.symm
  have hnt : Nontrivial C := CFSG.LocalCores.isQuasisimple_nontrivial hCn.1
  exact (Subgroup.nontrivial_iff_ne_bot C).mp hnt hbot

end CFSG.StandardType
