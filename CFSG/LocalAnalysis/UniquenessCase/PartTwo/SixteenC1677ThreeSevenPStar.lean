module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSevenCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSevenDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s168e3_seven_exists_inPStar {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) {r : ℕ} (hr : 2 ≤ r) (hr5 : r ≤ 5)
    (hE : IsElemAbelianOfRank 7 r ↥(lBar V₀ V hV L))
    (hsym : SymSumOfConj (Mbar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) r 3) :
    ∃ Y : Subgroup G, InPStar D V₀ Y := by
  have hH : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  have hMs : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := s15_Three_cTilde_normal hV hMs
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 c.std.h127 hH
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 7 (F11.O2p 7 D.M)
  obtain ⟨Xbar, hXn, hXe, hXc, hXd, hXL⟩ := s168e3_seven_exists_xbar c hs hr hE
  haveI := hXn
  have hXM : D.M ≤ normalizer ((F11.barPreimage11 D.M V₀ V Xbar : Subgroup G) : Set G) :=
    fun g hg => uc22p22u_mem_normalizer_barPreimage11 hg
  refine ⟨F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar), ?_⟩
  have hY11 := s16e_d3_inP11 D c.std.hSg (c.std.h1219 V₀ V hH) c.std.h1110 c.std.h77 hH11
    (by norm_num) (by norm_num) (by omega : 1 < r) Xbar hXn hXe hXc hXd hP
  by_cases hV0 : V₀ = ⊥
  · subst hV0
    have hcore := c.std.h1110 ⊥ V hH11 7 (by norm_num) (by norm_num) P hP
    obtain ⟨hexp, -, hcardY, -⟩ := hcore.2.2 r (by omega) Xbar hXn hXe hXc hXd
    have hPM : P ≤ D.M := (uc22p22u_sylow_O2p (by norm_num) (by norm_num) hP).1
    have hYle : F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar) ≤ P := by
      refine (Subgroup.closure_le P).2 fun x hx => ?_
      exact (inf_le_left.trans inf_le_left :
        (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar : Subgroup G) ≤ P) hx.1
    have hYp : IsPGroup 7
        (F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar)) :=
      hP.isPGroup.to_le hYle
    refine ⟨hY11, fun _ => ⟨7, by norm_num, hYp, ?_⟩⟩
    by_cases hbig : 7 ^ 2 < Nat.card ↥(F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓
        F11.barPreimage11 D.M ⊥ V Xbar))
    · exact Or.inl hbig
    · have hr2 : r = 2 := by
        have h1 : 7 ^ r ≤ 7 ^ 2 := hcardY.trans (not_lt.1 hbig)
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 7)).1 h1
        omega
      subst hr2
      obtain ⟨Δ, σ, hctx⟩ := s16e_d3_exists_ctx D hV c.setting hs hr hr5 hE
        (by rw [s16c1610_dParam_seven]; exact hsym)
      have hY49 : Nat.card ↥(F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓
          F11.barPreimage11 D.M ⊥ V Xbar)) = 49 :=
        le_antisymm (not_lt.1 hbig) hcardY
      have hcard : Nat.card ↥(Mbar D.M ⊥ V hV) ∣ 7 ^ 3 * 3 * Nat.factorial 3 :=
        s16e_d3_card_dvd_seven_pow_mul_three_mul_factorial hctx
      by_cases hYK : F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar) ⊓
          F11.CTilde D.M ⊥ V = ⊥
      · refine Or.inr (Or.inl (s168e3_seven_cond_ii hMs hcard (hYle.trans hPM) hYp ?_ hYK))
        exact s11_TenP_permutes (by norm_num) (by norm_num) hP hXM D.sylowM
      · exact (s168e3_seven_false_of_cent c hctx hXM hXL hP hcore.2.1.1 hexp hY49 hYK).elim
  · exact (inPStar_iff_of_ne_bot hV0 _).2 hY11

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
