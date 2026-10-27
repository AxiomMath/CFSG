module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c34_four_le_rk_vtil (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) :
    4 ≤ rk (Vtil V₀ V h.hyp125.isElemAbelian) := by
  set hV := h.hyp125.isElemAbelian with hVdef
  set hpf := h.hyp125.pairFacts with hpfdef
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  by_contra hlt
  have hrk3 : rk (Vtil V₀ V hV) ≤ 3 := by omega
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have hprank : CFSG.Open.pRank p (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) ≤ 1 :=
    s16c34_pRank_le_one (s15_Infra_vtil_sq_eq_one V₀ V hV) hrk3 hpP hp2
  have hcardV₀ : Nat.card V₀ ≤ 4 := by
    have h2 : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hpf.elemAbelian₀.isPGroup
    rw [h2, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) h.small
  obtain ⟨-, hle, hge⟩ :=
    uc22p22q_r115_of D hx h61 V₀ V (Hyp125.hyp11 h127 h.hyp125) hcardV₀ p hp
  have hle' : CFSG.Open.pRank p D.M - 1 ≤
      CFSG.Open.pRank p (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) := by
    rw [← s15_Three_pRank_MBar11 (D := D) hV hMs p]
    exact hle
  omega

theorem s16c34_one_lt_s15_of_rk_wTil_le_three (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hL : barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥)
    (hrk : rk ↥(wTil V₀ V h.hyp151.isElemAbelian L) ≤ 3) :
    1 < s15 D.M V₀ V h.hyp151.isElemAbelian L := by
  have hpos := s15_Eleven_pos_s D h.hyp151 h.hyp151.isElemAbelian
  by_contra hnot
  have hs : s15 D.M V₀ V h.hyp151.isElemAbelian L = 1 := by omega
  have htop := c8_wTil_eq_top D h1217 h.hyp151 h.hyp151.isElemAbelian hL hs
  have h4 : 4 ≤ rk (Vtil V₀ V h.hyp151.isElemAbelian) :=
    s16c34_four_le_rk_vtil D hx h61 h127 h.hyp16
  rw [htop, rk_top] at hrk
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
