module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Inner
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.LocalRank.InvolutionCentralizerLocalRank
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONAut.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem card_le_three_of_isCyclic_outer {H : Type*} [Group H] [Finite H]
    (h3H : ¬ 3 ∣ Nat.card H) (hout : IsCyclic (Outer H))
    {E : Subgroup (MulAut H)} (hE : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 3 := by
  classical
  haveI : IsCyclic (Outer H) := hout
  have hEp : IsPGroup 3 E := fun x =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hE x x.2)⟩
  have hinner : Nat.card (inner H) ∣ Nat.card H :=
    Subgroup.card_dvd_of_surjective (f := (MulAut.conj : H →* MulAut H).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  have hdisj : E ⊓ inner H = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hEp.to_le inf_le_left :
      IsPGroup 3 (E ⊓ inner H : Subgroup (MulAut H)))
    have hdvd : Nat.card (E ⊓ inner H : Subgroup (MulAut H)) ∣ Nat.card H :=
      (Subgroup.card_dvd_of_le inf_le_right).trans hinner
    rw [hk] at hdvd
    rcases k with _ | k
    · rwa [pow_zero, Subgroup.card_eq_one] at hk
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero k)).trans hdvd) h3H
  have hinj : Function.Injective ((QuotientGroup.mk' (inner H)).comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : (x : MulAut H) ∈ E ⊓ inner H :=
      ⟨x.2, (QuotientGroup.eq_one_iff _).1 hx⟩
    rw [hdisj] at hmem
    exact Subtype.ext (Subgroup.mem_bot.1 hmem)
  have hcyc : IsCyclic ↥E :=
    isCyclic_of_injective ((QuotientGroup.mk' (inner H)).comp E.subtype) hinj
  obtain ⟨g, hg⟩ := hcyc.exists_ofOrder_eq_natCard
  have hg3 : g ^ 3 = 1 := Subtype.ext (hE (g : MulAut H) g.2)
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  rw [hg] at hdvd
  exact Nat.le_of_dvd (by norm_num) hdvd

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
