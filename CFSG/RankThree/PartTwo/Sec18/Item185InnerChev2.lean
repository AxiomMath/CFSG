module

public import CFSG.RankThree.PartTwo.Sec18.Item185InnerCensus
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Rank2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowL52
public import CFSG.RankThree.PartOne.LIT.RankPSL3
public import CFSG.RankThree.PartOne.LIT.RankSuzuki
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (RankHyp Alt42Seven Alt42Eight)
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (NoE27 AutNoE27)

section RankMatrix

theorem noE27_projSL_three_two {n : ℕ} (hn : 1 ≤ n) : NoE27 (projSL 3 (GaloisField 2 n)) := by
  exact noE27_of_openPRank_le_two
    (CFSG.RankThree.PartOne.LIT.pRank_projSL_three_le (K := GaloisField 2 n) (f := n) hn
      (GaloisField.card 2 n (by omega)) Nat.prime_three (by norm_num))

theorem noE27_projSU_three_two {n : ℕ} (hn : 1 ≤ n) : NoE27 (projSU 3 2 n) := by
  exact noE27_of_openPRank_le_two (CFSG.RankThree.PartOne.LIT.pRank_projSU_three_le hn
    Nat.prime_three (by norm_num))

theorem noE27_projSp_two_two {n : ℕ} : NoE27 (projSp 2 (GaloisField 2 n)) := by
  exact noE27_of_openPRank_le_two (CFSG.RankThree.PartOne.LIT.pRank_projSp_two_le
    (K := GaloisField 2 n) Nat.prime_three (by norm_num)
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)))

end RankMatrix

section RankExc


theorem noE27_of_rankLE2 {K : Type} [Group K]
    (h : LieType.SeitzGeneration.RankLE2 3 K) : NoE27 K := by
  intro D hD
  have h9 := h D hD.1
  rw [hD.2] at h9
  norm_num at h9

theorem noE27_isoGTwo_two {X : Type} [Group X] {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    (h : Sec4.IsoGTwo X q) : NoE27 X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact noE27_of_rankLE2 (LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm
    (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_cat_G2 q hv (by omega)))

theorem noE27_trialityD4_two {X : Type} [Group X] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p = 2)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) : NoE27 X := by
  exact noE27_of_rankLE2 (LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv (by omega)))

theorem noE27_suzuki {X : Type} [Group X] [Finite X] {m : ℕ}
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) : NoE27 X := by
  exact noE27_of_openPRank_le_two (CFSG.RankThree.PartOne.LIT.pRank_le_two_of_suzuki hv e
    Nat.prime_three (by norm_num))

theorem noE27_reeF4 {X : Type} [Group X] {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) : NoE27 X := by
  exact noE27_of_rankLE2 (LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv))

theorem noE27_tits {X : Type} [Group X] (hv : TauCeti.LieTypeIndex.tits.Valid)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) : NoE27 X := by
  exact noE27_of_mulEquiv e fun D hD =>
    CFSG.HardMathSupport.Timmesfeld.CrossChar.no_elemAbelian27_cat_tits hv hD.1 hD.2

end RankExc

section Cases


theorem innerCase_seven (hU42 : NormIrred (projSU 4 2 1)) (hU48 : NormIrred (projSU 4 2 3)) :
    InnerCase Alt42Seven := by
  intro X _ _ hX A B c hd hP
  have hq := hd.quotient hX
  rcases hP with ⟨n, hn, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨q, hq2, hG⟩ | ⟨q, hv, hq2, ⟨φ⟩⟩ |
    ⟨m, hv, ⟨φ⟩⟩ | ⟨m, hv, ⟨φ⟩⟩ | ⟨hv, ⟨φ⟩⟩
  · exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (noE27_projSL_two_of_ne_three (by omega)))
      _ _ _ hq
  · exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (noE27_projSL_three_two hn)) _ _ _ hq
  · exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (noE27_projSU_three_two hn)) _ _ _ hq
  · exact noInnerData_of_noE27 (noE27_of_mulEquiv φ noE27_projSp_two_two) _ _ _ hq
  · by_cases h1 : n = 1
    · subst h1; exact (NormIrred.of_mulEquiv φ hU42).noInnerData _ _ _ hq
    · by_cases h3 : n = 3
      · subst h3; exact (NormIrred.of_mulEquiv φ hU48).noInnerData _ _ _ hq
      · exact Sec19.SimsC198.false_of_rankHyp_PSU4_two hX hn h1 h3 φ
  · exact noInnerData_of_noE27 (noE27_isoGTwo_two hq2 hG) _ _ _ hq
  · exact noInnerData_of_noE27 (noE27_trialityD4_two hv hq2 φ) _ _ _ hq
  · haveI : Finite (X ⧸ Subgroup.center X) := inferInstance
    exact noInnerData_of_noE27 (noE27_suzuki hv φ) _ _ _ hq
  · exact noInnerData_of_noE27 (noE27_reeF4 hv φ) _ _ _ hq
  · exact noInnerData_of_noE27 (noE27_tits hv φ) _ _ _ hq

theorem innerCase_eight (hL6 : NormIrred (projSL 6 (GaloisField 2 1)))
    (hL7 : NormIrred (projSL 7 (GaloisField 2 1))) (hSp6 : NormIrred (projSp 3 (GaloisField 2 1)))
    (hOm : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
      NormIrred (projOmegaMinus 3 (GaloisField 2 1) b c))
    (hL44 : NormIrred (projSL 4 (GaloisField 2 2))) : InnerCase Alt42Eight := by
  intro X _ _ hX A B c hd hP
  have hq := hd.quotient hX
  rcases hP with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨b, c', hbc, ⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ |
    ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact noInnerData_of_noE27 (noE27_of_mulEquiv φ Sec4.RonanK429.noE27_projSL_five_two)
      _ _ _ hq
  · exact Sec19.SimsC198.false_of_rankHyp_PSU5_two hX le_rfl φ
  · exact (NormIrred.of_mulEquiv φ hL6).noInnerData _ _ _ hq
  · exact Sec19.SimsC198.false_of_rankHyp_PSU6_two hX φ
  · exact (NormIrred.of_mulEquiv φ hL7).noInnerData _ _ _ hq
  · exact (NormIrred.of_mulEquiv φ hSp6).noInnerData _ _ _ hq
  · exact Sec19.SimsC198.false_of_rankHyp_Sp8_two hX φ
  · exact Sec19.SimsC198.false_of_rankHyp_OmegaPlus_two hX φ
  · exact (NormIrred.of_mulEquiv φ (hOm b c' hbc)).noInnerData _ _ _ hq
  · exact (NormIrred.of_mulEquiv φ hL44).noInnerData _ _ _ hq
  · exact Sec19.SimsC198.false_of_rankHyp_Sp6_four hX φ
  · exact Sec19.SimsC198.false_of_rankHyp_PSU5_two hX (by norm_num) φ
  · exact Sec19.SimsC198.false_of_rankHyp_PSU5_two hX (by norm_num) φ
  · exact Sec19.SimsC198.false_of_rankHyp_F4_two hX φ

end Cases

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
