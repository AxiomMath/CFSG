module

public import CFSG.LocalAnalysis.StandardType.GGSixD4SmallVacuous
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSpEight
public import CFSG.LocalAnalysis.StandardType.GGRootPlaneOm
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SylowFive
public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.Timmesfeld.Transvection.PresSp
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual
public import CFSG.RankThree.PartOne.KE.EDualStabilizer
public import CFSG.RankThree.PartOne.N143X.RankHelpers
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.LieType.Universal.Spin CFSG.Timmesfeld.ClassicalOrders
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

private theorem not_dvd_card_spSixFour :
    ¬ 5 ^ 4 ∣ Nat.card (StatedSp 3 (GaloisField 2 2)) := by
  rw [card_statedSp (K := GaloisField 2 2) 3, GaloisField.card 2 2 (by norm_num)]
  decide

private theorem not_dvd_card_spinSixTwo :
    ¬ 5 ^ 4 ∣ Nat.card (spinGroup (quadPlus 6 (GaloisField 2 1))) := by
  have hcard := CFSG.LieType.SeitzGeneration.ExcHigh.card_spinGroup_quadPlus_eq_mul
    (K := GaloisField 2 1) (n := 6) (by norm_num)
  rw [RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo
    (K := GaloisField 2 1) (n := 6) (by norm_num), Subgroup.card_bot, mul_one] at hcard
  rw [hcard]
  have h := card_statedProj_statedOmega_quadPlus (K := GaloisField 2 1) (n := 6) (by norm_num)
  rw [GaloisField.card 2 1 (by norm_num)] at h
  have h' : Nat.card (StatedProj (StatedOmega (StatedQuadPlus 6 (GaloisField 2 1)))) =
      2 ^ 30 * (2 ^ 6 - 1) * ∏ i ∈ Finset.Icc 1 5, (2 ^ (2 * i) - 1) := by
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [h]
    norm_num
  rw [h']
  decide

section Inputs

theorem ggSix_false_of_spSixFour {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {ψ : (ggU .PSp 3 2).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSp 3 2).D .PSp 3 2 ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p = 5) : False := by
  have hp' : p.Prime := hctx.1.2.2.2.2.2.1.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot
      (K := GaloisField 2 2) (n := 3) (by norm_num)).le
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := bstar_le_range_of_inner hC fun b hb =>
    PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 2) (n := 3) (by norm_num) ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb)
  have hpow : p ^ 4 ∣ Nat.card Bs := by
    have hcardBs := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp' hctx.2.1.2.1
    rw [hcardBs]
    refine Nat.pow_dvd_pow p ?_
    have hle : p ^ 4 ≤ p ^ CFSG.Open.pRank p Bs := by
      rw [← hcardBs]
      exact ggSixCtxV2_card_bstar hctx
    exact (Nat.pow_le_pow_iff_right hp'.one_lt).mp hle
  have hBdvd : Nat.card Bs ∣ Nat.card ψ.range := Subgroup.card_dvd_of_le hBψ
  have hUeq : Nat.card ψ.range = Nat.card (StatedSp 3 (GaloisField 2 2)) :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hdvdU : p ^ 4 ∣ Nat.card (StatedSp 3 (GaloisField 2 2)) := hUeq ▸ (hpow.trans hBdvd)
  rw [hp] at hdvdU
  exact not_dvd_card_spSixFour hdvdU

theorem ggSix_false_of_plusSixTwo {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ψ : (ggU .POmegaPlus 6 1).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .POmegaPlus 6 1).D .POmegaPlus 6 1 ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p = 5) : False := by
  have hp' : p.Prime := hctx.1.2.2.2.2.2.1.1
  revert ψ
  rw [ggU_POmegaPlus_eq (n := 6) (f := 1) (by norm_num)]
  intro ψ hctx
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo
      (K := GaloisField 2 1) (n := 6) (by norm_num)).le
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := bstar_le_range_of_inner hC fun b hb =>
    PsiDiag.SpinP.exists_mem_centralizer (K := GaloisField 2 1) (n := 6) (by norm_num) ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb)
  have hpow : p ^ 4 ∣ Nat.card Bs := by
    have hcardBs := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp' hctx.2.1.2.1
    rw [hcardBs]
    refine Nat.pow_dvd_pow p ?_
    have hle : p ^ 4 ≤ p ^ CFSG.Open.pRank p Bs := by
      rw [← hcardBs]
      exact ggSixCtxV2_card_bstar hctx
    exact (Nat.pow_le_pow_iff_right hp'.one_lt).mp hle
  have hBdvd : Nat.card Bs ∣ Nat.card ψ.range := Subgroup.card_dvd_of_le hBψ
  have hUeq : Nat.card ψ.range = Nat.card (spinGroup (quadPlus 6 (GaloisField 2 1))) :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hdvdU : p ^ 4 ∣ Nat.card (spinGroup (quadPlus 6 (GaloisField 2 1))) :=
    hUeq ▸ (hpow.trans hBdvd)
  rw [hp] at hdvdU
  exact not_dvd_card_spinSixTwo hdvdU

theorem ggSix_false_of_spTwoThree {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ} (hn : n = 3 ∨ n = 4)
    {ψ : (ggU .PSp n 1).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSp n 1).D .PSp n 1 ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p = 3) : False := by
  obtain ⟨-, -, ⟨-, -⟩, ⟨hrange, hker⟩, -⟩ := hctx.2
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have h9iii : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J := by
    intro d hd hd1 g hg
    refine s1.2.1.mem_of_conj_mem hd hd1 ?_
    have hgd : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have : g⁻¹ * d * g = d := by
      rw [mul_assoc, ← hgd, inv_mul_cancel_left]
    rw [this]
    exact s1.2.1.1 hd
  have h4 : GGTwoLocalRankFour p (Subgroup.normalizer (ψ.range : Set G)) := by
    rw [hrange]
    exact hctx.twoLocalRankFour h9iii
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot
      (K := GaloisField 2 1) (n := n) hn1).le
  rw [hp] at h4
  exact (ggSpSixEightRankInput_holds G n ψ hn hψinj hC) h4

theorem ggSix_false_of_plusFourFour {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ψ : (ggU .POmegaPlus 4 2).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .POmegaPlus 4 2).D .POmegaPlus 4 2 ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p = 5) : False :=
  ggSix_false_of_plusFour hctx s1 (by rw [hp]; norm_num)

end Inputs

end CFSG.StandardType
