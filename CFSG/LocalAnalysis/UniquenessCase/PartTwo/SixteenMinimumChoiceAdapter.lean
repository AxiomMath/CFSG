module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenMinimumChoice
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNoncomponentMinimumCases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen3FCompStd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNonthinComponentSOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThinComponentDispatch
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenA
public import Certificates.Certificate431004
public import Certificates.Certificate17430
public import Certificates.Certificate9726
public import CFSG.GroupTheory.StronglyClosedTI.OddCore
public import CFSG.GroupTheory.ThreeTranspositions.Basic
public import CFSG.LieType.Universal.Spin
public import CFSG.LocalAnalysis.SeitzReduction.RankOneKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcEmb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3WJoin
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Bound
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Move
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoLem
public import CFSG.Quasithin.H13.A6S13821zz10
public import CFSG.Quasithin.H13.A6S13821zz3
public import CFSG.Quasithin.H13.A6S13821zz4
public import CFSG.Quasithin.H13.A6S13821zz9
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Core
public import CFSG.RankThree.PartOne.TAIL.KSideCen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r16_3FE_of_component_dispatchers
    {G : Type} [Group G] [Finite G]
    (D : Data G) (hstd : S168e3Std D) (h136 : W4Lem13_6)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hthin : ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V),
      S168e3Ctx D V₀ V L hV →
      IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV) →
      (∀ q : ℕ, q.Prime → q ≠ 2 →
        CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1) →
      Concl163F D V₀ V hV L)
    (hnonthin_one : ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V),
      S168e3Ctx D V₀ V L hV →
      IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV) →
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
        2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L)) →
      s15 D.M V₀ V hV L = 1 →
      Concl163F D V₀ V hV L) :
    R16_3FE D := by
  have hminimum : MinChoiceSupport.R4_136Min D :=
    MinChoiceSupport.r4_136Min_holds D hstd.hx hstd.h61 hstd.h127 hstd.h1214 h136
  intro V₀ V L hV hS _ _
  obtain ⟨Lmin, hSmin, hnemin, hMin⟩ := hminimum V₀ V hS.hyp16
  let cmin : S168e3Ctx D V₀ V Lmin hV := ⟨hstd, hSmin, hnemin, hMin.toConc4_136⟩
  by_cases hcomp : IsComponentOf (lBar V₀ V hV Lmin) (Mbar D.M V₀ V hV)
  · by_cases hnonthin : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
        2 ≤ CFSG.Open.pRank q (lBar V₀ V hV Lmin)
    · by_cases hs : 1 < s15 D.M V₀ V hV Lmin
      · have hdone : Concl163F D V₀ V hV Lmin :=
          r16_3FComp_of_std_of_r880 D hstd h880 V₀ V Lmin hV hSmin
            hMin.toConc4_136 hs hcomp hnonthin
        exact ⟨Lmin, hSmin, hnemin, hMin.toConc4_136, hdone⟩
      · have hs1 : s15 D.M V₀ V hV Lmin = 1 := by
          have hpos : 0 < s15 D.M V₀ V hV Lmin :=
            s15_Eleven_pos_s D hSmin.hyp151 hV
          omega
        have hdone : Concl163F D V₀ V hV Lmin :=
          hnonthin_one V₀ V Lmin hV cmin hcomp hnonthin hs1
        exact ⟨Lmin, hSmin, hnemin, hMin.toConc4_136, hdone⟩
    · have hthinPred : ∀ q : ℕ, q.Prime → q ≠ 2 →
          CFSG.Open.pRank q (lBar V₀ V hV Lmin) ≤ 1 := by
        intro q hq hq2
        by_contra hle
        exact hnonthin ⟨q, hq, hq2, by omega⟩
      have hdone : Concl163F D V₀ V hV Lmin :=
        hthin V₀ V Lmin hV cmin hcomp hthinPred
      exact ⟨Lmin, hSmin, hnemin, hMin.toConc4_136, hdone⟩
  · exact s168e3_exists_concl163F_of_noncomponent_minimum cmin hMin hcomp

section CertificateUnion

theorem r16_3FE_of_std_of_r82_of_r869_of_r880
    {G : Type} [Group G] [Finite G]
    (D : Data G) (hstd : S168e3Std D) (h136 : W4Lem13_6)
    (h82 : F08.R82 D) (h869 : F08.R869 D) (h880 : F08.R880 D) :
    R16_3FE D :=
  r16_3FE_of_component_dispatchers D hstd h136 h880
    (fun _V₀ _V _L _hV c hcomp hthin =>
      s168e3_concl163F_of_thin_component c h82 hcomp hthin)
    (fun _V₀ _V _L _hV c hcomp hnonthin hs1 =>
      s168e3_concl163F_of_nonthin_component_of_s15_eq_one
        c h82 h869 h880 hcomp hs1 hnonthin)

end CertificateUnion
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
