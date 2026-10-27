module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213d
import CFSG.GroupTheory.PGroup.PrimePartTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s21rs2_hyp2120_of {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    (h1 : ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M)
    (h2 : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal ∧
      ¬ ∃ n : ℕ, Odd n ∧ (IsSp4 (Bar2 L) n ∨ IsSU3 (Bar2 L) n))
    (h0 : ∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) : Hyp2120 D c := by
  refine ⟨h1, h2, fun p hp => ?_, fun p hp h => ?_⟩
  · haveI := Fact.mk (D.sig_prime p hp).1
    refine ⟨⊥, CFSG.ABGLocalTools.isSylowOf_of_card bot_le ?_, bot_le⟩
    rw [Subgroup.card_bot, Nat.factorization_eq_zero_of_not_dvd
      (CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero (D.sig_prime p hp).1 (h0 p hp)), pow_zero]
  · rw [h0 p hp] at h
    omega

theorem uc22s21rs2_exists_pair (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h21E : S21_21E D Ch) (h8E : S21_8E D Ch) (h9 : S21_9N D Ch) (h17 : S21_17 D Ch)
    (h1930 : H1930 D) (he : 3 < CFSG.Open.evenRank G) (c : Ctx21 D Ch)
    (hS1 : ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M)
    (hU3 : ∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) :
    ∃ L ∈ calC D.M, (conjSetOf D.M L).ncard = 2 ∧
      ∃ n : ℕ, 2 < n ∧ (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) := by
  by_contra hno
  have hnorm : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal := by
    intro L hL
    rcases h17 h1930 c L hL with h | ⟨h2, hn⟩ | ⟨-, -, -, -, hev, -⟩
    · exact uc22p21j_normal_of_conjClosure_eq hL.1.le h
    · exact absurd ⟨L, hL, h2, hn⟩ hno
    · omega
  refine uc22p2213d_false_of_hyp2120 D Ch h21E h1930 he c ?_
  refine uc22s21rs2_hyp2120_of c hS1 (fun L hL => ⟨hnorm L hL, ?_⟩) hU3
  rintro ⟨n, hn, hsp | hsu⟩
  · exact uc22p2213d_false_of_sp4 D Ch hx h8E h1930 he c hL hn hsp
  · exact uc22p2213d_false_of_su3 D Ch h9 h1930 he c hL (hnorm L hL) hn hsu

end CFSG.LocalAnalysis.UniquenessCase.UC22
