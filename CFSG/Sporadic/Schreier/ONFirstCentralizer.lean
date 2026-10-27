module

public import CFSG.Sporadic.Schreier.ONCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.PerfectCentralQuotientOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierCharacteristic

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Assembly.LowTwoRank

theorem lQuot_classicalModel :
    StatedClassicalModel (onL ⧸ Subgroup.center onL) .PSL 3 2 2 := by
  obtain ⟨hadm, K, hK, hfin, hcard, ⟨e⟩⟩ := onX_classicalModel
  exact ⟨hadm, K, hK, hfin, hcard, ⟨lQuotEquiv.trans e⟩⟩

theorem onL_outer_solvable :
    Group.IsSolvable (Outer onL) :=
  (CFSG.LocalAnalysis.ComponentInitial.perfect_central_quotient_Schreier onL).2.2
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.linear_higher_classical_model_schreier
      le_rfl lQuot_classicalModel).2

theorem centralizer_L_le :
    Subgroup.centralizer ((onL.subgroupOf onM : Subgroup onM) : Set onM) ≤ onL.subgroupOf onM := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  have hc : (x : Equiv.Perm (Fin N)) ∈
      onM ⊓ Subgroup.centralizer (onL : Set (Equiv.Perm (Fin N))) := by
    refine Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have := Subgroup.mem_centralizer_iff.1 hx ⟨y, onL_le_M hy⟩ (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hy)
    exact congrArg Subtype.val this
  rw [onM_centralizer_L] at hc
  exact onQ_le_L hc

theorem at_on_first_centralizer_schreier :
    Group.IsSolvable (Outer onM) := by
  have hD : Group.IsSolvable (Outer (onL.subgroupOf onM)) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
      (Subgroup.subgroupOfEquivOfLe onL_le_M)).2.2 onL_outer_solvable
  exact CFSG.ComponentClassification.CatalogueSchreierCharacteristic.outer_solvable
    (onL.subgroupOf onM) centralizer_L_le hD

end CFSG.ONSchreier
