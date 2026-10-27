module

public import CFSG.Quasithin.EmptyFaithful.S152RDef
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsAction
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.LinearGroups.UnitaryThreeOverNine CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem card_centralizer_involution_statedSU_three_three {F : Type} [Field F] (hF : Nat.card F = 9)
    {l : StatedSU 3 3 F} (hl : orderOf l = 2) :
    Nat.card (Subgroup.centralizer ({l} : Set (StatedSU 3 3 F))) = 96 := by
  have h := unitaryFieldData_of_card hF
  have hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) ![1, 0, 0] ![1, 0, 0] ≠ 0 := by
    rw [gramForm_e0_left]
    exact one_ne_zero
  let L₀ : NonisoLine F := lineOf _ hv
  have hL₀ : L₀.1 = F ∙ ![1, 0, 0] := rfl
  have h96 := card_centralizer_tauLine (h := h) (hF := hF) hL₀
  have hconj := isConj_of_orderOf_eq_two hF hl (tauLine h hF L₀).2
  rw [card_centralizer_singleton_eq_of_isConj hconj]
  exact h96

theorem noE9CentralizedByInvolution_of_isPSU_three_three {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU 3 3 1) : NoE9CentralizedByInvolution X := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hF9 : Nat.card F = 9 := by rw [hF]; norm_num
  have hbot := statedScalars_subgroupOf_statedSU_eq_bot hF9
  let e2 : StatedProj (StatedSU 3 3 F) ≃* StatedSU 3 3 F :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine NoE9CentralizedByInvolution.of_mulEquiv (e.trans e2) ?_
  refine noE9CentralizedByInvolution_of_not_dvd fun l hl2 hl1 hdvd => ?_
  have hord : orderOf l = 2 := orderOf_eq_prime (by rw [pow_two]; exact hl2) hl1
  rw [card_centralizer_involution_statedSU_three_three hF9 hord] at hdvd
  omega

end CFSG.Quasithin
