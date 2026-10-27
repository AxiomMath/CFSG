module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.RankThree.PartOne.S12.SectionalRank
import CFSG.RankThree.PartOne.LIT.KFCGTList
import CFSG.GH74.EvenRank
import CFSG.Assembly.OpenBridges
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.Yardstones.Mf4cdcdf2e013

open Subgroup
open CFSG.LocalAnalysis.RankThreeUC (hSet)

variable {G : Type} [Group G] [Finite G]

theorem exists_maxLocal_mem_sigma {p : ℕ} (hp : p ∈ CFSG.Open.uniqueFourBeta G) :
    ∃ M : Subgroup G, CFSG.Open.uniqueFourIsMaxTwoLocal M ∧ p ∈ CFSG.Open.uniqueFourSigma M := by
  obtain ⟨B, hB⟩ := CFSG.PreuniquenessRankFour.Helpers.betaFour_has_bmax (G := G) hp
  obtain ⟨U, hU1, hU2, hBU⟩ := hB.2.2
  obtain ⟨M, hNM, hM⟩ := CFSG.PreuniquenessRankFour.Helpers.exists_maximal_twoLocal (G := G)
    (H := normalizer (U : Set G)) ⟨U, hU1, hU2, rfl⟩
  exact ⟨M, hM, hp, B, hB, hBU.trans hNM⟩

theorem exists_sigmaChoice4 (he : 4 ≤ CFSG.Open.evenRank G) :
    ∃ p ∈ CFSG.Open.uniqueFourBeta G, SigmaChoice4 G p := by
  by_cases h3 : 3 ∈ CFSG.Open.uniqueFourBeta G
  · exact ⟨3, h3, fun _ => rfl, fun h => absurd h3 h⟩
  by_cases hq : ∃ q, SigmaTwo4 G q
  · obtain ⟨q, hq'⟩ := hq
    exact ⟨q, hq'.1, fun h => absurd h h3, fun _ _ => hq'⟩
  · obtain ⟨p, hp⟩ := CFSG.PreuniquenessRankFour.Helpers.betaFour_nonempty (G := G) he
    exact ⟨p, hp, fun h => absurd h h3, fun _ h => absurd h hq⟩

theorem exists_not_isTI4 (hS : Standing4 G) (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) {M : Subgroup G}
    (hM : CFSG.Open.uniqueFourIsMaxTwoLocal M) :
    ∃ V : Subgroup G, V ≤ M ∧ M ≤ normalizer (V : Set G) ∧ CFSG.Open.IsElemAbelian 2 V ∧
      ¬ CFSG.CGT.Timmesfeld75.IsTI V := by
  have := hS.simple
  obtain ⟨B, hB⟩ := (Set.toFinite {W : Subgroup G | W ≤ M ∧ M ≤ normalizer (W : Set G) ∧
    CFSG.Assembly.IsElemAbelian 2 W}).exists_maximal
      ⟨⊥, bot_le, (normalizer_eq_top_iff (H := (⊥ : Subgroup G)).mpr inferInstance).symm ▸ le_top,
        ⟨⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [mem_bot.mp hx, one_pow]⟩⟩
  refine ⟨B, hB.1.1, hB.1.2.1, hB.1.2.2, fun hTI => hcat ?_⟩
  have hK : CFSG.IsKProper G := CFSG.ComponentClassification.CatalogueKProper.isKProper_of_kProper
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.mp hS.kProper)
  exact (hGF G hS.nonab hK (CFSG.GH74.isCharTwoType_iff.mp hS.charTwo) M
    (CFSG.LocalAnalysis.RankThreeUC.isMaximalTwoLocal_of_rankThreeIsMaxTwoLocal hM) B hB hTI).2

theorem hSet_nonempty_of_pushingUp (hS : Standing4 G)
    (hPU : CFSG.RankThree.PartOne.PushingUpCorollary) {M T : Subgroup G} (hM : M ≠ ⊤)
    (hTG : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) : (hSet T M).Nonempty := by
  have := hS.simple
  by_contra hempty
  have hloc : ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → T ≤ H → H ≤ M := by
    intro H hH hTH
    by_contra hHM
    exact hempty ⟨H, hTH, hHM, hS.charTwo H hH⟩
  obtain ⟨T', hTT'⟩ := hTG.isPGroup.exists_le_sylow
  have hTeq : (T' : Subgroup G) = T := hTG.eq_of_le hTT' le_top T'.isPGroup'
  have hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G :=
    (CFSG.Assembly.kProper_inCatalog_iff_isKProper G).2 hS.kProper
  have hc : CFSG.Assembly.IsCharTwoType G := (CFSG.Assembly.isCharTwoType_iff_open G).2 hS.charTwo
  have hT₁ : ∀ T₁ : Subgroup G, T₁ ≠ ⊥ →
      T₁ ≤ CFSG.RankThree.PartOne.pushingUpS (T' : Subgroup G) →
      (T₁.subgroupOf (CFSG.RankThree.PartOne.pushingUpS (T' : Subgroup G))).Characteristic →
        normalizer (T₁ : Set G) ≤ M := by
    intro T₁ hT₁1 hT₁S hT₁char
    have hT₁2 : IsPGroup 2 T₁ :=
      (T'.isPGroup'.to_le (CFSG.RankThree.PartOne.Sec15Final.pushingUpS_le _)).to_le hT₁S
    have hTN : T ≤ normalizer (T₁ : Set G) := hTeq ▸
      (le_normalizer.trans (CFSG.RankThree.PartOne.Sec15Final.normalizer_le_normalizer_pushingUpS
        _)).trans (CFSG.RankThree.PartOne.Sec15Final.normalizer_le_normalizer_of_characteristic
          hT₁S hT₁char)
    exact hloc _ ⟨T₁, hT₁1, hT₁2, rfl⟩ hTN
  have hT₂ : ∀ T₂ : Subgroup G, T₂ ≠ ⊥ →
      T₂ ≤ CFSG.RankThree.PartOne.omegaOneCenterIn (T' : Subgroup G) →
        centralizer (T₂ : Set G) ≤ M := by
    intro T₂ hT₂1 hT₂le
    have hT₂2 : IsPGroup 2 T₂ :=
      T'.isPGroup'.to_le (hT₂le.trans (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le _))
    have hTC : T ≤ centralizer (T₂ : Set G) := hTeq ▸
      (CFSG.LocalAnalysis.RankThreeUC.le_centralizer_omegaOneCenterIn _).trans
        (centralizer_le fun _ hx => hT₂le hx)
    exact (centralizer_le_normalizer _).trans
      (hloc _ ⟨T₂, hT₂1, hT₂2, rfl⟩ (hTC.trans (centralizer_le_normalizer _)))
  have h4 : 4 ≤ CFSG.Assembly.evenRank G := (CFSG.Assembly.evenRank_eq_open G).symm ▸ hS.rank
  rcases hPU G hK hc T' M hM hT₁ hT₂ with h | h | h
  · have := CFSG.RankThree.PartOne.kfCGTList G hc (Or.inl h)
    omega
  · have := CFSG.RankThree.PartOne.kfCGTList G hc (Or.inr h)
    omega
  · have := CFSG.RankThree.PartOne.evenRank_le_two_of_sectionalTwoRankLEFour hc h
    omega

theorem uniqueness_exclusion_of_yardstones
    (hD : AGL81TheoremDFour) (hC : AGL81TheoremCFour) (hcat : CatalogNoUniqueFour)
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement)
    (hPU : CFSG.RankThree.PartOne.PushingUpCorollary) (h614 : Theorem614Four)
    (h82 : Theorem82Four) (h1669 : Theorem1669Four) (h1930 : Theorem1930Four)
    (h2219 : Theorem2219Four) (h23 : Section23Four) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
        ¬ CFSG.Open.uniqueFourUnique G := by
  intro G _ _ hsimple hnonab hK hchar he hU
  have hS : Standing4 G := ⟨hsimple, hnonab, hK, hchar, he⟩
  by_cases hcG : CFSG.Blueprint.Catalog G
  · exact hcat G hS hcG hU
  obtain ⟨p, hp, hpc⟩ := exists_sigmaChoice4 he
  obtain ⟨M, hM, hpM⟩ := exists_maxLocal_mem_sigma hp
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 M
  have hN := hD G hS hU p M hM hpM T hT
  have hTG := CFSG.LocalAnalysis.RankThreeUC.isSylowOf_top_of_normalizer_le hT hN
  obtain ⟨V, hVM, hMV, hVe, hVTI⟩ := exists_not_isTI4 hS hGF hcG hM
  have hH := hSet_nonempty_of_pushingUp hS hPU
    (CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hnonab M hM.1) hTG
  let S : Setup4 G := ⟨p, M, hM, hpM, T, hT, hTG, hN, hcG, hH, V, hVM, hMV, hVe, hVTI⟩
  have hMS : S.InMSigma := hpc
  have hCM : TheoremCAt S.M := hC G hS hU p M hM hpM
  have h614M := h614 G hS hU S hMS hCM
  have hI : PartIAt S.M := ⟨hCM, h614M, h82 G hS hU S hMS hCM h614M⟩
  have hsmall := h1930 G hS hU S hMS hI (h1669 G hS hU S hMS hI)
  exact h23 G hS hU S hMS hI hsmall (h2219 G hS hU S hMS hI hsmall)

end CFSG.Yardstones.Mf4cdcdf2e013
