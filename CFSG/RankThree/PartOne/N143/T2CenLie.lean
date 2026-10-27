module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Small
public import CFSG.LieType.SeitzGeneration.UnitaryHyperDiag
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Basic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.Holt.Centralizer
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.StronglyEmbedded
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.RankThree.PartOne.N143.T2

open CFSG CFSG.Assembly CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25Ns (IsLThreeEps)

theorem finiteField_card_primePow (K : Type) [Field K] [Finite K] :
    ∃ p n : ℕ, p.Prime ∧ 1 ≤ n ∧ Nat.card K = p ^ n := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hn⟩ := FiniteField.card' K
  refine ⟨p, (n : ℕ), hp, ?_, ?_⟩
  · have := n.pos
    omega
  · rw [Nat.card_eq_fintype_card]
    exact hn

theorem pRank_three_le_two_of_isLThreeEps {Y : Type} [Group Y] [Finite Y] (h : IsLThreeEps Y) :
    CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2 := by
  obtain ⟨K, _, hK, hmod, ⟨e⟩⟩ | ⟨K, _, hK, q, hcard, hq, ⟨e⟩⟩ := h
  ·
    obtain ⟨p, f, hp, hf, hKc⟩ := finiteField_card_primePow K
    have hmod' : p ^ f % 3 = 1 := by
      rw [← hKc]
      exact hmod
    have h3 : 3 ∣ p ^ f - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have hr := CFSG.SectionRank.QTK.CentreFact.small_pRank_three_statedSL_le_two
      hp hf hKc h3
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e).trans_le hr
  ·
    obtain ⟨p, n, hp, -, hKc⟩ := finiteField_card_primePow K
    have hpn : p ^ n = q ^ 2 := hKc.symm.trans hcard
    have hqdvd : q ∣ p ^ n := by
      rw [hpn]
      exact dvd_pow_self q two_ne_zero
    obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hqdvd
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | hpos
      · rw [pow_zero] at hq
        omega
      · omega
    have hcard' : Nat.card K = p ^ (2 * f) := by
      rw [hcard, ← pow_mul, Nat.mul_comm]
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K := ⟨hp, hf, hcard'⟩
    have h3 : 3 ∣ p ^ f + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have hr := CFSG.LieType.SeitzGeneration.pRank_three_projSU_three_le hU h3
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e).trans_le hr

theorem pRank_three_le_two_of_lie_cover {K : Type} [Group K] [Finite K]
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.LocalAnalysis.RankThreeTheoremC.IsLinThreeCover3 d)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 :=
  pRank_three_le_two_of_isLThreeEps
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.isLThreeEps_of_isLinThreeCover3 hd e)

end CFSG.RankThree.PartOne.N143.T2
