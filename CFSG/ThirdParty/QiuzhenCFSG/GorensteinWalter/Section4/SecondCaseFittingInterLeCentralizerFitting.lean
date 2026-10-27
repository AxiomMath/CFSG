module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The equation-(3) intersection lies in the local Fitting subgroup

The subgroup `F(U) ∩ M` is normal and nilpotent in `C_M(t)`, so it lies in
the Fitting subgroup of `C_M(t)`.  This is the Fitting hypothesis needed by
the PSL2 form of Fact 1.10(ii).
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The equation-(3) Fitting intersection lies in the Fitting subgroup of
the involution centralizer inside the second-case maximal subgroup. -/
public theorem secondCase_fitting_inter_le_centralizer_fitting
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c) :
    fittingSubgroupOf c.U ⊓ w.M ≤
      fittingSubgroupOf
        (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M) := by
  let C : Subgroup G := Subgroup.centralizer ({c.t} : Set G) ⊓ w.M
  let Y : Subgroup G := fittingSubgroupOf c.U ⊓ w.M
  have hYleC : Y ≤ C := by
    intro y hy
    have hyH : y ∈ c.H :=
      (centralizerSetup_FU_isNormalIn_H c).1 hy.1
    refine ⟨?_, hy.2⟩
    rw [← c.H_eq_centralizer]
    exact hyH
  have hYnormalC : IsNormalIn Y C := by
    refine ⟨hYleC, ?_⟩
    intro z hz y hy
    have hzH : z ∈ c.H := by
      rw [c.H_eq_centralizer]
      exact hz.1
    exact ⟨
      (centralizerSetup_FU_isNormalIn_H c).2 z hzH y hy.1,
      w.M.mul_mem (w.M.mul_mem hz.2 hy.2) (w.M.inv_mem hz.2)⟩
  have hYleFU : Y ≤ fittingSubgroupOf c.U := inf_le_left
  have hYnil : Group.IsNilpotent Y := by
    let Y0 : Subgroup c.FU := Y.subgroupOf c.FU
    have : Group.IsNilpotent c.FU := by
      change Group.IsNilpotent ((fittingSubgroup c.U).map c.U.subtype)
      have : Group.IsNilpotent (fittingSubgroup c.U) := by infer_instance
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.equivMapOfInjective
          (fittingSubgroup c.U) c.U.subtype c.U.subtype_injective)
    have hY0nil : Group.IsNilpotent Y0 := Subgroup.isNilpotent Y0
    let eY : Y0 ≃* Y := Subgroup.subgroupOfEquivOfLe hYleFU
    exact Group.nilpotent_of_mulEquiv (G := Y0) (G' := Y) eY
  exact le_fittingSubgroupOf_of_isNormalIn_nilpotent hYleC hYnormalC hYnil

end CFSG.GorensteinWalter
