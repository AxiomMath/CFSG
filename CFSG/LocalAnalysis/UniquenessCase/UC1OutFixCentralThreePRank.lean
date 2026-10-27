module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K341
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeCover
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeSU
import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.NoncyclicCentre
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBFrontier
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCoverWideHolds
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryCover

public section

namespace CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree

open CFSG CFSG.RankThree.PartTwo.Sec4

theorem fixCommInner_of_isoLThreePi_full
    {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X)) {z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3) {p f : ℕ} [Fact p.Prime]
    (hf : 1 ≤ f) (hpi : IsoLThreePi (X ⧸ Subgroup.center X) p f) : FixCommInner X z := by
  have hq2 := two_lt_of_isoLThreePi hq hf hpi
  have hZ : Subgroup.center X ≠ ⊥ := by
    intro hbot
    have hz1 : z = 1 := by simpa [hbot] using hz
    rw [hz1, orderOf_one] at hz3
    norm_num at hz3
  have : Group.IsPerfect X := hq.1
  rcases hpi with ⟨hlin, ⟨e⟩⟩ | ⟨huni, ⟨e⟩⟩
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hodd : Odd (Nat.card (Subgroup.center X)) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ3
      rw [hn]
      exact Odd.pow (by decide)
    exact fixCommInner_of_isSLThreeEpsAt Fact.out hf hq2
      (Census.isSLThreeEpsAt_of_linear hodd hZ hf hlin e) hz hz3
  · let h := unitaryFieldData_galoisField p f hf
    obtain ⟨ε⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary.exists_mulEquiv_unitarySU_three
      h hq2 hq.1.commutator_eq_top (e.trans (projSUEquivUnitaryPSU p f h)) hZ
    exact FixCommInner.of_mulEquiv ε.symm
      (fixCommInner_unitarySU h hq2 (map_mem_center_of_mulEquiv ε.symm hz)
        (by rw [MulEquiv.orderOf_eq, hz3]))

end CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree
open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating


theorem outFixCentralThreePRank_holds : OutFixCentralThreePRank := by
  intro X _ _ hq hcat hr z hz hz3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hqY, ⟨ε⟩, hzY⟩ := quotient_centerThreePrime_facts hq hz
  let Y := X ⧸ centerThreePrime X
  change (z : Y) ∈ Subgroup.center Y at hzY
  have hcatY : CFSG.Open.IsCatalogGroup (Y ⧸ Subgroup.center Y) :=
    CFSG.Assembly.inCatalog_isoInvariant ε hcat
  have hqY' : CFSG.Open.IsQuasisimple Y := ⟨hqY.1.commutator_eq_top, hqY.2.1⟩
  have hrY : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (centerThreePrime X) not_three_dvd_card_centerThreePrime]
    exact hr
  have hzY3 : orderOf (z : Y) = 3 := orderOf_mk_centerThreePrime hz3
  have hZ3 : IsPGroup 3 (Subgroup.center Y) := isPGroup_center_quotient_centerThreePrime hq
  have hZ : Subgroup.center Y ≠ ⊥ := by
    intro hbot
    have hz1 : (z : Y) = 1 := Subgroup.mem_bot.mp (hbot ▸ hzY)
    rw [hz1, orderOf_one] at hzY3
    norm_num at hzY3
  have hcyc : IsCyclic (Subgroup.center Y) := by
    by_contra hnc
    have := KFactProofs.T29.noncyclicCentreRank_of_tables
        (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
        (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
            CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds) Y hqY' hcatY hZ3 hnc
    omega
  have : Group.IsPerfect Y := hqY.1
  apply FixCommInner.of_centerThreePrime hq
  rcases KFactProofs.Stroth.TripleCover.kFactAlphaListM3Wide_holds Y hqY' hcatY hZ hZ3 hcyc hrY with
    hA6 | hA7 | hM22 | hON | ⟨⟨d, hd⟩, hlin, ⟨e⟩⟩
  · obtain ⟨e⟩ := hA6
    exact fixCommInner_of_card_outer_le_four e
      (DegreeSix.outer_card_le_four_of_equiv (MulEquiv.refl _)) _
  · obtain ⟨e⟩ := hA7
    have h2 := outer_card_dvd_two_of_equiv_outside_six (n := 7) (Or.inr le_rfl) (MulEquiv.refl _)
    exact fixCommInner_of_card_outer_le_four e
      ((Nat.le_of_dvd (by norm_num) h2).trans (by norm_num)) _
  · obtain ⟨e⟩ := hM22
    obtain ⟨f⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    have h2 : Nat.card (Outer CFSG.Blueprint.NativeSporadic.M22) ≤ 2 :=
      card_outer_le_two_of_card_mulAut_le CFSG.Sporadic.Schreier.m22_center_eq_bot'
        CFSG.Sporadic.Schreier.m22_mulAut_card
    exact fixCommInner_of_card_outer_le_four (e.trans f.symm) (h2.trans (by norm_num)) _
  · obtain ⟨e⟩ := hON
    obtain ⟨f⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    exact @fixCommInner_of_card_outer_le_four Y _ _ Units.instGroup _ _ (e.trans f.symm)
      (Nat.le_of_dvd (by norm_num) CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1) _
  · rcases hlin with ⟨q, hq, h3⟩ | ⟨q, hq, h3⟩
    · change d = _ at hq
      subst d
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      exact fixCommInner_of_isoLThreePi_full hqY hZ3 hzY hzY3 q.exponent_pos
        (Census.isoLThreePi_of_A2 hd h3 e)
    · change d = _ at hq
      subst d
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      exact fixCommInner_of_isoLThreePi_full hqY hZ3 hzY hzY3 q.exponent_pos
        (Census.isoLThreePi_of_twistedA2 hd h3 e)

theorem k341_holds : K341 :=
  k341_of_outFixCentralThreePRank outFixCentralThreePRank_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
