module

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Basic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Context
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem normalizer_alpha_ne_top {E₀ : Subgroup G}
    (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hαne : thetaAlpha 3 E₀ ≠ ⊥)
    (hαsolv : Group.IsSolvable ↥(thetaAlpha 3 E₀)) :
    Subgroup.normalizer (thetaAlpha 3 E₀ : Set G) ≠ ⊤ := by
  intro htop
  haveI : IsSimpleGroup G := hsimple
  have hnormal : (thetaAlpha 3 E₀).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have htop' : thetaAlpha 3 E₀ = ⊤ := by
    haveI : (thetaAlpha 3 E₀).Normal := hnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top (thetaAlpha 3 E₀) with h | h
    · exact absurd h hαne
    · exact h
  have hGsolv : Group.IsSolvable G := by
    haveI : Group.IsSolvable ↥(⊤ : Subgroup G) := htop' ▸ hαsolv
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := G)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := G)).symm.injective
  have hcomm : ∀ a b : G, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr hGsolv
  obtain ⟨a, b, hne⟩ := hnonab
  exact hne (hcomm a b)

theorem normalizer_alpha_le_M_of_L_le (hKF7 : UC22.KF7Use D)
    (c : Ctx82E3 D) (h7 : D.sig = {7})
    {E₀ : Subgroup G}
    (hHne : Subgroup.normalizer (thetaAlpha 3 E₀ : Set G) ≠ ⊤)
    (hL : c.L ≤ Subgroup.normalizer (thetaAlpha 3 E₀ : Set G))
    (hrankL : 2 ≤ CFSG.Open.pRank 7 c.L) :
    Subgroup.normalizer (thetaAlpha 3 E₀ : Set G) ≤ D.M := by
  classical
  let H : Subgroup G := Subgroup.normalizer (thetaAlpha 3 E₀ : Set G)
  change H ≤ D.M
  by_contra hHM
  have h7mem : 7 ∈ D.sig := by rw [h7]; exact Set.mem_singleton 7
  have hrank : 1 < CFSG.Open.pRank 7 (H ⊓ D.M) := by
    have hmono : CFSG.Open.pRank 7 c.L ≤ CFSG.Open.pRank 7 (H ⊓ D.M) :=
      CFSG.SectionRank.pRank_mono (p := 7) (by norm_num) (le_inf hL c.hyp81.1)
    omega
  have hsec : UC22.F07.Sec7Hyp D 7 H :=
    ⟨by norm_num, by norm_num, c.isStronglyPEmbedded_of_mem_sigma h7mem, hHne, hHM, hrank⟩
  have hsol : Group.IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 7 ↥H))) := by
    rcases hKF7 7 h7mem H hsec with h | ⟨h75, -⟩
    · exact h
    · omega
  exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.eight70_not_isSolvable
    (p := 7) (M := D.M) (H := H) (X := c.L) (by norm_num)
    (le_inf hL c.hyp81.1) c.hyp81.2.2.1 (by omega) hsol

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
