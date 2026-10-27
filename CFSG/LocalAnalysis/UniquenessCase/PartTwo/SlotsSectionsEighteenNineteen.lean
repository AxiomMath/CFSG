module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.AdapterThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem ascSectionNineteenConditional_of_sec19
    (h : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), CFSG.Open.rankThreeUC G →
      ∀ S : Setup G, S.InMSigma → S19.Sec19ContraOf1669 (dataOfSetup hS S)) :
    CFSG.Yardstones.Me2c15c2c995a.AscSectionNineteenConditional := by
  unfold CFSG.Yardstones.Me2c15c2c995a.AscSectionNineteenConditional
  intro G _ _ hS hUC S hMS V₀ V h125 hcard hbar
  refine h G hS hUC S hMS V₀ V ?_ hcard ?_
  · exact ⟨(hyp123_iff S.witness.maxLocal S.T V₀ V).1 h125.1, h125.2⟩
  · exact fun hsmall => (mBarGT3_iff S.M V₀ V).1 (hbar hsmall)

theorem ascEighteenTwentyFourConditional_of_r1824
    (h : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), CFSG.Open.rankThreeUC G →
      ∀ S : Setup G, S.InMSigma → S18.R18_24Of1669 (dataOfSetup hS S)) :
    CFSG.Yardstones.Me2c15c2c995a.AscEighteenTwentyFourConditional := by
  unfold CFSG.Yardstones.Me2c15c2c995a.AscEighteenTwentyFourConditional
  intro G _ _ hS hUC S hMS V₀ V h125 hcard hbar
  have h125' : Hyp125 (dataOfSetup hS S) V₀ V :=
    ⟨(hyp123_iff S.witness.maxLocal S.T V₀ V).1 h125.1, h125.2⟩
  have hbar' : MBarGT (dataOfSetup hS S).M V₀ V 3 :=
    (mBarGT3_iff S.M V₀ V).1 hbar
  have hbig : 1 < mSub V₀ := h G hS hUC S hMS V₀ V h125' hbar'
  have hpf := hyp123_pairFacts h125'.1
  have hsmall : mSub V₀ ≤ 1 :=
    (S18.mSub_le_one_iff hpf.elemAbelian₀).2 hcard
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
