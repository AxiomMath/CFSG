module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVKit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVTorus
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
import CFSG.RankThree.PartTwo.Census.TripleCoverU62
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks
import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSU f4TwoIndex primePowerTwo)
open Item434Kit Item434Alt

namespace Item434SmallTwoIV

theorem not_isThreeCenterCover_of_tripleCoverLie (hT : Census.TripleCoverLie)
    (d : TauCeti.ValidLieTypeIndex) (hd : ¬ Census.TripleCoverLieIndex d.1) {S : Type}
    [Group S] (ι : (TauCeti.CFSGIndex.lie d).Group ≃* S) (J : Type) [Group J] [Finite J]
    (hJ : Census.IsThreeCenterCover J S) : False := by
  obtain ⟨hq, h3, ⟨e⟩⟩ := hJ
  exact hd (hT d J ⟨hq, h3, ⟨e.trans ι.symm⟩⟩)

@[expose] def primePowerEight : TauCeti.PrimePower :=
  ⟨2, 3, Nat.prime_two, by norm_num⟩

noncomputable def u52CarrierEquiv :
    (TauCeti.CFSGIndex.lie ⟨.twistedA 4 primePowerTwo, by simp⟩).Group ≃* projSU 5 2 1 :=
  have : Fact (Nat.Prime primePowerTwo.p) := ⟨Nat.prime_two⟩
  CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 4 primePowerTwo (by simp)

noncomputable def u62CarrierEquiv :
    (TauCeti.CFSGIndex.lie ⟨.twistedA 5 primePowerTwo, by simp⟩).Group ≃* projSU 6 2 1 :=
  have : Fact (Nat.Prime primePowerTwo.p) := ⟨Nat.prime_two⟩
  CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 5 primePowerTwo (by simp)

noncomputable def u58CarrierEquiv :
    (TauCeti.CFSGIndex.lie ⟨.twistedA 4 primePowerEight, by simp [primePowerEight]⟩).Group ≃*
      projSU 5 2 3 :=
  have : Fact (Nat.Prime primePowerEight.p) := ⟨Nat.prime_two⟩
  CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 4 primePowerEight
    (by simp [primePowerEight])

theorem not_isThreeCenterCover_u52 (hT : Census.TripleCoverLie) (J : Type) [Group J] [Finite J]
    (hJ : Census.IsThreeCenterCover J (projSU 5 2 1)) : False :=
  not_isThreeCenterCover_of_tripleCoverLie hT _ (by simp [Census.TripleCoverLieIndex])
    u52CarrierEquiv J hJ

theorem not_isThreeCenterCover_u58 (hT : Census.TripleCoverLie) (J : Type) [Group J] [Finite J]
    (hJ : Census.IsThreeCenterCover J (projSU 5 2 3)) : False :=
  not_isThreeCenterCover_of_tripleCoverLie hT _ (by simp [Census.TripleCoverLieIndex])
    u58CarrierEquiv J hJ

theorem not_isThreeCenterCover_f42 (hT : Census.TripleCoverLie) (J : Type) [Group J] [Finite J]
    (hJ : Census.IsThreeCenterCover J (TauCeti.CFSGIndex.lie f4TwoIndex).Group) : False :=
  not_isThreeCenterCover_of_tripleCoverLie hT f4TwoIndex (fun h => h) (MulEquiv.refl _) J hJ

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem center_layer_eq_bot_of_u48
    (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 4 2 3) :
    Subgroup.center (layer G) = ⊥ := by
  have hK : Nat.card (GaloisField 2 (2 * 3)) = (2 ^ 3) ^ 2 := by
    rw [GaloisField.card 2 (2 * 3) (by norm_num)]
    norm_num
  have hD := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot
    (K := GaloisField 2 (2 * 3)) (2 ^ 3)
  let ε : StatedProj (StatedSU 4 (2 ^ 3) (GaloisField 2 (2 * 3))) ≃*
      StatedSU 4 (2 ^ 3) (GaloisField 2 (2 * 3)) :=
    (QuotientGroup.quotientMulEquivOfEq hD).trans QuotientGroup.quotientBot
  let θ : layer G ⧸ Subgroup.center (layer G) ≃* CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * 3)) 2 3) 4 :=
    e₀.trans ((projSUEquivStatedProj 4 2 3).trans
      (ε.trans (CFSG.LieType.Universal.Unitary.equivStatedSU hK 4).symm))
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hker : (QuotientGroup.mk' (Subgroup.center (layer G))).ker = Subgroup.center (layer G) :=
    QuotientGroup.ker_mk' _
  have hodd : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center (layer G))).ker) := by
    rw [hker]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨α', hα', -⟩ := CFSG.SectionRank.EvenCover.even_su_existsUnique_lift hK (by norm_num)
    (by decide : Even 4) (QuotientGroup.mk'_surjective (Subgroup.center (layer G))) hker.le hodd
    θ.symm.toMonoidHom
  have hα'x : ∀ y, QuotientGroup.mk' (Subgroup.center (layer G)) (α' y) = θ.symm y := fun y =>
    DFunLike.congr_fun hα' y
  have htop : α'.range = ⊤ := by
    refine CFSG.SectionRank.EvenCover.eq_top_of_forall_mul_center fun x => ⟨α' (θ x), ⟨_, rfl⟩, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h1 := hα'x (θ x)
    rw [QuotientGroup.mk'_apply, MulEquiv.symm_apply_apply] at h1
    rw [h1, inv_mul_cancel]
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨y, hy⟩ := htop ▸ Subgroup.mem_top z
  have h1 := hα'x y
  rw [hy, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz] at h1
  have hy1 : y = 1 := by
    have := congrArg θ h1
    rw [map_one, MulEquiv.apply_symm_apply] at this
    exact this.symm
  rw [Subgroup.mem_bot, ← hy, hy1, map_one]

end Item434SmallTwoIV

open Item434SmallTwoIV

section Families


theorem item434SmallTwoIV_U62_9 : Item434SecForCard IsSmallTwoU62 9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  obtain ⟨e₀⟩ := hL
  have hZ : Subgroup.center (layer G) = ⊥ :=
    Item434Spor.center_layer_eq_bot_of_rankFour hc (S := projSU 6 2 1)
      (fun J _ _ ⟨hq, h3, ⟨e⟩⟩ => Census.tripleCoverU62RankFour primePowerTwo (by simp) rfl rfl
        J ⟨hq, h3, ⟨e.trans u62CarrierEquiv.symm⟩⟩)
      e₀ (Item434Spor.twoLocalOddRank_layer_le_three hG₀ H f hf hker)
  obtain ⟨D, hD, hD27⟩ := Item434Spor.exists_e27_of_two_lt_pRank (X := projSU 6 2 1)
    (by have := Census.three_lt_pRank_projSU_six_two; omega)
  exact (Item434Spor.false_of_card_nine hc hZ e₀ hD hD27 h9).elim

theorem item434SmallTwoIV_U48_9 : Item434SecForCard IsSmallTwoU48 9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  obtain ⟨e₀⟩ := hL
  obtain ⟨D, hD, hD27⟩ := exists_elemAbelian_projSU_torus 3 2 3 (by norm_num) (by norm_num)
    (by norm_num)
  exact (Item434Spor.false_of_card_nine hc (center_layer_eq_bot_of_u48 hc e₀) e₀ hD
    (by rw [hD27]; norm_num) h9).elim

theorem item434SmallTwoIV_U58_9_of (hT : Census.TripleCoverLie) : Item434SecForCard IsSmallTwoU58 9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  obtain ⟨e₀⟩ := hL
  have hZ := center_layer_eq_bot_of_no_cover hc (not_isThreeCenterCover_u58 hT) e₀
  obtain ⟨E, hE, hE81⟩ := exists_elemAbelian_projSU_torus 4 2 3 (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨D, hD, hD27⟩ := exists_e27_of_e81 hE (by rw [hE81]; norm_num)
  exact (Item434Spor.false_of_card_nine hc hZ e₀ hD hD27 h9).elim

theorem item434SmallTwoIV_F42_9_of
    (hT : Census.TripleCoverLie) : Item434SecForCard IsSmallTwoF42 9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  obtain ⟨e₀⟩ := hL
  have hZ := center_layer_eq_bot_of_no_cover hc (not_isThreeCenterCover_f42 hT) e₀
  obtain ⟨D, hD, hD27⟩ := Item434Spor.exists_e27_of_two_lt_pRank
    (X := (TauCeti.CFSGIndex.lie f4TwoIndex).Group)
    (by have := Census.three_lt_pRank_f4Two; omega)
  exact (Item434Spor.false_of_card_nine hc hZ e₀ hD hD27 h9).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
