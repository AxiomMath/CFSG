module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUNotDvd
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

section Components

variable {U : Type*} [Group U]

private theorem isComponentOf_subgroupOf_top {X : Type*} [Group X] {A K : Subgroup X}
    (h : IsComponentOf A K) : CFSG.Open.IsComponentOf (A.subgroupOf K) ⊤ := by
  refine ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib h.2.1.subgroupOf, ?_⟩
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.2

theorem isComponentOf_eq_of_perfect_le [Finite U] {C Y Z J' : Subgroup U}
    (hY : IsComponentOf Y C) (hZ : IsComponentOf Z C) (hJ'Y : J' ≤ Y) (hJ'Z : J' ≤ Z)
    (hperf : ⁅J', J'⁆ = J') (hne : J' ≠ ⊥) : Z = Y := by
  by_contra hZY
  have hZ' := isComponentOf_subgroupOf_top hZ
  have hY' := isComponentOf_subgroupOf_top hY
  have hne' : Z.subgroupOf C ≠ Y.subgroupOf C := by
    intro h
    have h' := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hZ.1, inf_eq_left.mpr hY.1] at h'
    exact hZY h'
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hZ' hY' hne'
  have hmap := congrArg (Subgroup.map C.subtype) hcomm
  simp only [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hZ.1,
    Subgroup.map_subgroupOf_eq_of_le hY.1, Subgroup.map_bot] at hmap
  have hbot : ⁅J', J'⁆ = ⊥ :=
    le_antisymm ((Subgroup.commutator_mono hJ'Z hJ'Y).trans hmap.le) bot_le
  exact hne (hperf.symm.trans hbot)

end Components

end CFSG.StandardType.TableCRes
