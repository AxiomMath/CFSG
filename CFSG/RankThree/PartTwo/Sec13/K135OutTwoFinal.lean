module

public import CFSG.RankThree.PartTwo.Sec13.K135OutTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallF3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodG2
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporOut

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open TauCeti CFSG.RankThree.PartOne.OutStructure
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section


theorem outTwoInputs_holds : OutTwoInputs where
  ree := by
    intro hr Y _ f
    exact CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF3.isCyclic_outer_reeG2 hr f
  g2 := by
    intro q hv Y _ g
    exact OutPNice.of_mulEquiv g
      (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.outPNice_cat_G2 q hv Nat.prime_two)
  d4 := by
    intro q hv hp2 Y _ f
    have hce : CFSG.Blueprint.ChevalleyExceptionalModel Y .trialityD4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hp2 (by decide) f⟩
    rw [hp2] at hce
    exact outPNice_trialityD4 Nat.prime_two hce
  sz := by
    intro m hv Y _ f
    exact outPNice_Suzuki Nat.prime_two (CFSG.StandardType.ChevTwo.suzukiModel_of_valid m hv f)
  f4r := by
    intro m hv Y _ f
    exact outPNice_twistedF4 Nat.prime_two
      (CFSG.StandardType.ChevTwo.reeTitsModel_of_reeF4 m hv f)
  tits := by
    intro hv Y _ _ f
    exact (CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound Y 2 1
      (CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv f)).2.2.1
  f42 := by
    intro Y _ f
    have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 CFSG.Assembly.RankThreeEven.primePowerTwo
      CFSG.Assembly.RankThreeEven.f4TwoIndex.2 rfl f
    exact outPNice_F4 Nat.prime_two ⟨⟨Nat.prime_two, Nat.one_pos, rfl⟩, hmodel⟩
  spor := by
    intro s Y _ _ f
    obtain ⟨e⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
    exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.card_outer_dvd_two ⟨s, ⟨f.trans e.symm⟩⟩

theorem kFactOutTwo_holds : KFactOutTwo := kFactOutTwo_of_inputs outTwoInputs_holds

end

end CFSG.RankThree.PartTwo.Sec13.F135Last
