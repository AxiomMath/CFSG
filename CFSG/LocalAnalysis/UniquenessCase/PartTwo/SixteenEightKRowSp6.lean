module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Inputs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcEmb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKQuotMap
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKQuotFix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSp6Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16k_isSpn_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSpn X n a) : IsSpn Y n a := by
  obtain ⟨hev, K, hK, hKf, hcard, ⟨eS⟩⟩ := h
  exact ⟨hev, K, hK, hKf, hcard, ⟨e.symm.trans eS⟩⟩

theorem s16k_false_of_sp6 (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hSpC : RSp6SpinCent) (hSpF : RSp6SpinForm)
    (hSpSt : RSp6SpinStab)
    (hirr : commSub ⊤ (lBar V₀ V hV L) ∈ irrSet (lBar V₀ V hV L))
    (hS : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hm : E3.mQuot (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) = 8) : False := by
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hrk3 : 3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) := h.three_le_pRank hpσ
  obtain ⟨Q, hQc, hQf, L', N, hsq, hcardQ, ⟨eL⟩, hirrImp, hNL, hrank, -⟩ :=
    s16k_exists_quot_data h
  letI := hQc
  letI := hQf
  have hcardQ8 : Nat.card Q = 2 ^ 8 := by rw [hcardQ, hm]
  have hQrw : CFSG.Open.pRank p (⊥ : Subgroup (MulAut Q)) ≤ 0 :=
    CFSG.SectionRank.pRank_le hp.one_lt fun E hE _ => by rw [le_bot_iff.1 hE]; simp
  have hQrk : rk ↥(⊤ : Subgroup Q) = 8 := by
    unfold rk
    rw [Subgroup.card_top, hcardQ8]
    exact padicValNat.prime_pow 8
  haveI : Nontrivial Q :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hcardQ8]; norm_num)
  have hQirr : IsIrrOn L' ⊤ ⊥ := by
    refine ⟨bot_lt_top, ?_, ?_, ?_⟩
    · intro x _ u _; exact Subgroup.mem_top u
    · intro x _ u hu
      exact Subgroup.mem_bot.2 (by rw [Subgroup.mem_bot.1 hu, map_one])
    · intro J hJ _ _
      exact hirrImp hirr J (fun l hl b hb => hJ l hl b hb)
  have hLsp : IsSpn ↥L' 6 1 := s16k_isSpn_of_mulEquiv eL hS
  have hcent : Subgroup.centralizer (L' : Set (MulAut Q)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    exact hSpC Q hsq L' hLsp hQrk hQirr c
      (fun l hl => (Subgroup.mem_centralizer_iff.1 hc l hl).symm)
  have h1 := s16k_pRank_le_of_normalizer (Q := Q) (L' := L') (N := N) hNL hp
  rw [hcent, inf_bot_eq, Nat.eq_zero_of_le_zero hQrw, zero_add] at h1
  have h2 := s16k_pRank_aut_sp6 hS hp hp2
  rw [s16k_pRank_mulAut_congr eL p] at h2
  have h4 := hrank p hp
  have h5 : 3 ≤ if p = 3 then 3 else 1 := le_trans hrk3 (h4.trans (h1.trans h2))
  have hp3 : p = 3 := by
    by_contra hne
    rw [if_neg hne] at h5
    omega
  have hrk : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 3 := by
    have ha : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ CFSG.Open.pRank 3 N := by
      simpa [← hp3] using hrank p hp
    have hb : CFSG.Open.pRank 3 N ≤ 3 := by
      have hh := h1.trans h2
      rw [hp3] at hh
      simpa using hh
    exact ha.trans hb
  obtain ⟨Q₂, hQ2c, hQ2f, q, ρ, hqs, hqk, hρ, heq, hsq2, hcard2, hirr2⟩ :=
    s16k_exists_quot_map h
  letI := hQ2c
  letI := hQ2f
  have hcard2_8 : Nat.card Q₂ = 2 ^ 8 := by rw [hcard2, hm]
  have hρ_sp : IsSpn ↥ρ.range 6 1 := s16k_isSpn_of_mulEquiv (MonoidHom.ofInjective hρ) hS
  have hρ_rk : rk ↥(⊤ : Subgroup Q₂) = 8 := by
    unfold rk
    rw [Subgroup.card_top, hcard2_8]
    exact padicValNat.prime_pow 8
  haveI hQ2nt : Nontrivial Q₂ :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard2_8]; norm_num)
  have hρ_irr : IsIrrOn ρ.range ⊤ ⊥ := by
    refine ⟨bot_lt_top, ?_, ?_, ?_⟩
    · intro x _ u _; exact Subgroup.mem_top u
    · intro x _ u hu
      exact Subgroup.mem_bot.2 (by rw [Subgroup.mem_bot.1 hu, map_one])
    · intro J hJ _ _
      exact hirr2 hirr J (fun l b hb => hJ (ρ l) ⟨l, rfl⟩ b hb)
  have hfixQ : ∀ w : Q₂, w ≠ 1 → ∃ g ∈ ρ.range, orderOf g = 3 ∧ g w = w :=
    s16k_sp6_fix_ord hSpF hSpSt hsq2 hρ_sp hρ_rk hρ_irr
  have hne : ∃ w : Q₂, w ≠ 1 := by
    obtain ⟨w, hw⟩ := (nontrivial_iff_exists_ne (1 : Q₂)).1 hQ2nt
    exact ⟨w, hw⟩
  have hfixAbs : ∀ x : Vtil V₀ V hV, x ≠ 1 →
      ∃ y ∈ lBar V₀ V hV L, orderOf y = 3 ∧ y x = x :=
    s16k_transport_fix_ord_quot Nat.prime_three (by norm_num) hqs hqk hρ heq hne hfixQ
  have hcm := s16k_sp6_center_mult hGA hS
  have hz : Odd (Nat.card (Subgroup.center ↥(lBar V₀ V hV L))) := by
    rw [hcm.1]; exact odd_one
  have hmult : ¬ 3 ∣ Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) := by
    rw [hcm.2]; norm_num
  have hpσ3 : 3 ∈ D.sig := by rw [← hp3]; exact hpσ
  exact s16g_false_of_fix_lBar D h.std h.setting h.quasi hz Nat.prime_three (by norm_num)
    hpσ3 hmult (s16g_dvd_card_cTilde D h.std h.setting hpσ3 hrk) hfixAbs

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
