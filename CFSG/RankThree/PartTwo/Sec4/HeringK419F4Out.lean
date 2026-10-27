module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419Gen
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartOne.RF4.FinalKFacts
import CFSG.LieType.Ree.LargeReeInvolutionIntermediateOddCore

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringK419.ReeF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.LargeReeInvolution CFSG.RankThree.PartTwo.KFacts

section Ree


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem hasOuterWitness_fieldAut (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (σ : K ≃+* K) (hσ : σ ≠ 1) : HasOuterWitness (ReeTag.F4.reeGammaFieldAut K a σ) := by
  obtain ⟨c, hc⟩ : ∃ c : K, σ c ≠ c := by
    by_contra hcon
    push Not at hcon
    exact hσ (RingEquiv.ext hcon)
  have hz := centralZ_mem ha hK c
  refine ⟨(ReeTag.F4.reeFixedPosUnipotent K a).subgroupOf (ReeTag.F4.reeGamma K a),
    ReeTag.isPGroup_reeFixedPosUnipotent_subgroupOf, ?_,
    ⟨centralZ K a c, ReeTag.reeFixedPosUnipotent_le_reeGamma hz⟩, hz, fun h => hc ?_⟩
  · intro t ht
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact (ReeTag.map_reeFixedPosUnipotent_exactEntrywiseAut (t := ReeTag.F4) (a := a) σ).le
      (Subgroup.mem_map_of_mem _ ht)
  · have h1 := congrArg Subtype.val h
    rw [ReeTag.coe_reeGammaFieldAut, units_map_centralZ] at h1
    exact centralZ_injective h1

theorem hasOuterWitness_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : MulAut (ReeTag.F4.reeGamma K a)) (hα3 : α ^ 3 = 1) (hα : ¬ IsInnerAut α) :
    HasOuterWitness α := by
  obtain ⟨σ, hσ3, hinn⟩ := largeRee_order_three_inFieldCoset ha hK hα3 hα
  obtain ⟨x, hx⟩ := CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj a K hK σ hσ3 α hα3 hinn
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ3
    omega
  exact hasOuterWitness_of_conj (MulAut.conj x) _ α hx (hasOuterWitness_fieldAut ha hK σ hσ1)

theorem hasOuterWitness_of_reeTitsModel {X : Type} [Group X] {n : ℕ}
    (h : ReeTitsModel X CFSG.Open.StatedLieTag.twistedF4 2 n) (β : MulAut X) (hβ3 : β ^ 3 = 1)
    (hβ : ¬ IsInnerAut β) : HasOuterWitness β := by
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma h
  exact hasOuterWitness_of_mulEquiv e (hasOuterWitness_reeGamma ha hK _
    (by rw [← map_pow, hβ3, map_one]) fun h1 => hβ ((isInnerAut_congr e β).1 h1))

end Ree

end CFSG.RankThree.PartTwo.Sec4.HeringK419.ReeF4
