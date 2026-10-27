module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigModelB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11DimD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c11_normalizer_le_of_bigAlt (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (hsig : D.sig = {3})
    (hmB : MBarGT D.M V₀ V 1) {n : ℕ} (hn : n = 9 ∨ n = 10)
    {L₀ : Subgroup (MulAut (Vtil V₀ V hV))} {J₀ J₁ : Subgroup (Vtil V₀ V hV)}
    (hset : S16C11AltSetup n (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (kBar D.M V₀ V hV L) L₀ J₀ J₁) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hp3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have hP := h125.pairFacts
  have h4 : Nat.card V₀ ≤ 4 := by
    have h1 : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hP.elemAbelian₀.isPGroup
    have h2 : 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hc.setting.hyp16.small
    omega
  have hn9 : 9 ≤ n := by omega
  obtain ⟨Bb, hBbL, hBb3, hBbnc, hBb16⟩ := s16c11_big_exists_B hn hset
  obtain ⟨B, hBM, hBp, hBV₀, hBbar, hBnc⟩ := s16c11_exists_pGroup_lift D hV h125 h4 hset.l_le
    hset.cfg.perfect Nat.prime_three hBbL hBb3
  have h1 := s16c11_mSub_add_rk_fixV_le_rMV D hin.h61 hV h125 hp3 hBM hBp (hBnc hBbnc) hBV₀
  rw [hBbar] at h1
  have hrk8 : rk ↥(fixV Bb) = 8 := by
    have hcard : Nat.card ↥(fixV Bb) = 2 ^ 8 := by
      rw [s16c11_big_fixV_card hset (hBbL.trans hset.ll₀), hBb16]
      norm_num
    unfold rk
    rw [hcard]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact padicValNat.prime_pow 8
  rw [hrk8] at h1
  have hpR : CFSG.Open.pRank 2 (Mbar D.M V₀ V hV) ≤ 6 := by
    have := s16c11_big_pRank_le hset.dir hset.ksym hset.sym
    omega
  have hr : ((CFSG.Open.pRank 2 (Mbar D.M V₀ V hV) + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (show CFSG.Open.pRank 2 (Mbar D.M V₀ V hV) + mSub V₀ <
      mSub V₀ + 8 by omega)) h1
  have hD1 : S16C11DimD1 D V₀ V hV := by
    intro E hE _ _
    rcases hn with rfl | rfl
    · exact (s16c11_big_aSet_nine hset hE).elim
    · rw [s16c11_big_rkIdx_ten hset hE]
      omega
  have hTI : S16C11TI D V₀ V := by
    refine s16c11_tiConj_of_stronglyEmbedded D h125 (q := 3) (hin.hSg.sig1_sp 3 (hin.h1219 ▸ hp3))
      ?_
    intro _ w hw hw0
    obtain ⟨φ, hφL, hφ3, hφw⟩ := s16c11_big_exists_fixed_order_three hn9 hset
      (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩))
    exact s16c11_dvd_card_cent_of_fixed_order D (Hyp125.hyp11 hin.h127 h125) h4 hV
      Nat.prime_three (by norm_num) hw hw0 (hset.l_le hφL) hφ3 hφw
  exact s16c11_normalizer_le_of_dimD' D hin.h61 hV h125 hTI hmB hr hD1 hp3
    (hBbL.trans hset.l_le) hBb3 hBbnc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
