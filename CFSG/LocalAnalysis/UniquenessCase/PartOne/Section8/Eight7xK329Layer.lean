module

import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

private theorem k329la_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hp : Group.IsPerfect Q := ⟨hQ.1⟩
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  refine ⟨hp, hs, ?_⟩
  have := Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q)
  simpa only [isMulCommutative_iff, not_forall] using this

private theorem k329la_factor_normal_in_iSup {C : Type*} [Group C] {ι : Type*}
    (Lf : ι → Subgroup C) (hc : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥) (i : ι) :
    ((Lf i).subgroupOf (⨆ i, Lf i)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_iSup Lf i)]
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · subst hji
    exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hc j i hji)).trans
      (Subgroup.centralizer_le_normalizer (Lf i : Set C))

private theorem k329la_factor_isSubnormal {C : Type*} [Group C] {ι : Type*}
    (Lf : ι → Subgroup C) (hc : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥)
    (hLn : (⨆ i, Lf i).Normal) (i : ι) : (Lf i).IsSubnormal :=
  Subgroup.IsSubnormal.trans (le_iSup Lf i)
    (k329la_factor_normal_in_iSup Lf hc i).isSubnormal hLn.isSubnormal

private theorem k329la_factor_isComponent {C : Type*} [Group C] {ι : Type*}
    (Lf : ι → Subgroup C) (hq : ∀ i, CFSG.Open.IsQuasisimple ↥(Lf i))
    (hc : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥) (hLn : (⨆ i, Lf i).Normal) (i : ι) :
    CFSG.IsComponent (Lf i) :=
  ⟨k329la_isQuasisimple (hq i), k329la_factor_isSubnormal Lf hc hLn i⟩

theorem k329_solvable_normal_centralizes {C : Type} [Group C] [Finite C] {ι : Type} [Fintype ι]
    (Lf : ι → Subgroup C) (hq : ∀ i, CFSG.Open.IsQuasisimple ↥(Lf i))
    (hc : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥) (hLn : (⨆ i, Lf i).Normal)
    (N : Subgroup C) [N.Normal] (hN : IsSolvable ↥N) :
    ⁅N, ⨆ i, Lf i⁆ = ⊥ := by
  have hNs : N.IsSubnormal := (inferInstance : N.Normal).isSubnormal
  have hcent :=
    (CFSG.LocalCores.component_solvable_centralizer (G := C) (R := N) hN hNs).1
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (iSup_le fun i => Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (hcent (Lf i) (k329la_factor_isComponent Lf hq hc hLn i)))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
