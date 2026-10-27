module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieDefs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCSp
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthOdd
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthMinus
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCLin
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCUni

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

variable {X : Type} [Group X] [Finite X] {r f : ℕ}

theorem outerFixed3_psp6 (hr : r.Prime) (hr3 : r ≠ 3) (h : LieModel X .PSp 3 r f) :
    OuterFixed3 X := by
  intro ψ hψ hψI
  have hcl := h.statedClassicalModel_of_ne_zero (by norm_num)
  obtain ⟨-, F₀, _, _, hcard, hrk⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.psp_pRank_fixed hcl Nat.prime_three
      (by norm_num) ψ hψ hψI
  refine le_trans ?_ hrk
  have h3 : ¬ 3 ∣ Nat.card F₀ := by
    rw [hcard]
    intro hd
    exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)).symm
  rw [CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_Sp_formula
    Nat.prime_three (by norm_num) h3]
  have hz : ((Nat.card F₀ : ℕ) : ZMod 3) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact h3
  have hcases : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide
  rcases hcases _ hz with h1 | h2
  · rw [h1, orderOf_one]
    simp
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h22 : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
    rw [h2, h22]
    simp

theorem outerFixed3_omega7 (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : LieModel X .POmegaOdd 3 r f) : OuterFixed3 X := by
  intro ψ hψ hψI
  have hcl := h.statedClassicalModel_of_ne_zero (by norm_num)
  obtain ⟨-, F₀, hF₀, hF₀fin, hcard, hrk⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pomegaOdd_pRank_fixed hcl
      Nat.prime_three (by norm_num) ψ hψ hψI
  refine le_trans ?_ hrk
  have h3 : ¬ 3 ∣ Nat.card F₀ := by
    rw [hcard]
    intro hd
    exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)).symm
  have hF2 : (2 : F₀) ≠ 0 := by
    have hpF : ¬ 2 ∣ Nat.card F₀ := by
      rw [hcard]
      exact (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC.not_dvd_pow_of_ne
        (p := 2) Nat.prime_two hr hr2)
    have h :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC.natCast_ne_zero_of_not_dvd_card
        (F := F₀) (p := 2) Nat.prime_two hpF
    exact h
  rw [CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_OmegaOdd_formula
    Nat.prime_three (by norm_num) (by norm_num) hF2 h3]
  have hz : ((Nat.card F₀ : ℕ) : ZMod 3) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact h3
  have hcases : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide
  rcases hcases _ hz with h1 | h2
  · rw [h1, orderOf_one]
    simp
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h22 : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
    rw [h2, h22]
    simp

theorem outerFixed3_pomega8m (hr : r.Prime) (hr3 : r ≠ 3) (h : LieModel X .POmegaMinus 4 r f) :
    OuterFixed3 X := by
  intro ψ hψ hψI
  have hcl := h.statedClassicalModel_of_ne_zero (by norm_num)
  obtain ⟨-, F₀, hF₀, hF₀fin, hcard, b, c, hirr, hrk⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pomegaMinus_pRank_fixed hcl
      Nat.prime_three (by norm_num) ψ hψ hψI
  refine le_trans ?_ hrk
  have h3 : ¬ 3 ∣ Nat.card F₀ := by
    rw [hcard]
    intro hd
    exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)).symm
  have hz : ((Nat.card F₀ : ℕ) : ZMod 3) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact h3
  have hcases : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide
  have hdvd : ((3 : ℕ) : ℤ) ∣ (Nat.card F₀ : ℤ) ^ 4 + (-1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rcases hcases _ hz with h1 | h2
    · rw [h1]
      decide
    · rw [h2]
      decide
  rw [CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_OmegaMinus_formula
    Nat.prime_three (by norm_num) (by norm_num) hirr h3, if_pos hdvd]
  rcases hcases _ hz with h1 | h2
  · rw [h1, orderOf_one]
    simp
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h22 : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
    rw [h2, h22]
    simp

private theorem outerFixed3_psl4_aux_arith {q : ℕ} (hq : q % 3 = 1) :
    ((q : ℕ) : ZMod 3) = 1 ∧ ¬ 3 ∣ q ∧ 3 ∣ q - 1 := by
  have hqz : ((q : ℕ) : ZMod 3) = 1 := by
    rw [← ZMod.natCast_mod q 3, hq]
    norm_num
  have hge : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0] at hq; norm_num at hq
    · exact h0
  refine ⟨hqz, ?_, ?_⟩
  · intro hd
    rw [Nat.dvd_iff_mod_eq_zero] at hd
    exact absurd (hd.symm.trans hq) (by norm_num)
  · rw [← ZMod.natCast_eq_zero_iff]
    rw [Nat.cast_sub hge, Nat.cast_one, hqz, sub_self]

private theorem outerFixed3_psl4_aux_rank {F : Type} [Field F] [Finite F]
    (hpF : ¬ 3 ∣ Nat.card F) (hdiv : ¬ 3 ∣ Nat.gcd 4 (Nat.card F - 1))
    (hdvd : 3 ∣ Nat.card F - 1) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 4 F))) := by
  have hform := pRank_statedProj_SL_formula (F := F) (p := 3) (n := 4)
    Nat.prime_three (by norm_num) (by norm_num) hpF hdiv
  rw [if_pos hdvd] at hform
  rw [hform]

theorem outerFixed3_psl4 (hr : r.Prime) (hq : r ^ f % 3 = 1) (h : LieModel X .PSL 4 r f) :
    OuterFixed3 X := by
  intro ψ hψ hψI
  have hcl := h.statedClassicalModel_of_ne_zero (by norm_num)
  have hcl' := hcl
  obtain ⟨-, F, hF, hFin, hFcard, _⟩ := hcl'
  obtain ⟨_, hpq, hdvd0⟩ := outerFixed3_psl4_aux_arith hq
  have hpF : ¬ 3 ∣ Nat.card F := by rw [hFcard]; exact hpq
  have hdvd : 3 ∣ Nat.card F - 1 := by rw [hFcard]; exact hdvd0
  have hdiv : ¬ 3 ∣ Nat.gcd 4 (r ^ f - 1) := fun hd => by
    have h4 : 3 ∣ 4 := hd.trans (Nat.gcd_dvd_left 4 (r ^ f - 1))
    norm_num at h4
  have hdiv' : ¬ 3 ∣ Nat.gcd 4 (Nat.card F - 1) := by rw [hFcard]; exact hdiv
  obtain ⟨hpf, F₀, hF₀, hFin₀, hcard, hrank⟩ :=
    psl_three_pRank_fixed (n := 4) (by norm_num) hcl Nat.prime_three (by norm_num) hdiv ψ hψ hψI
  have hcard' : Nat.card F = Nat.card F₀ ^ 3 := by
    rw [hFcard, hcard, ← pow_mul, Nat.div_mul_cancel hpf]
  have heq := pRank_statedProj_SL_eq_of_pow (F := F) (F₀ := F₀) (p := 3) (n := 4)
    Nat.prime_three (by norm_num) (by norm_num) hcard' hpF hdiv'
  refine le_trans ?_ hrank
  rw [← heq]
  exact outerFixed3_psl4_aux_rank hpF hdiv' hdvd

private theorem outerFixed3_psl67_aux_arith {q : ℕ} (hq : q % 3 = 2) :
    ((q : ℕ) : ZMod 3) = 2 ∧ ¬ 3 ∣ q ∧ ¬ 3 ∣ q - 1 := by
  have hqz : ((q : ℕ) : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod q 3, hq]
    norm_num
  have hge : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0] at hq; norm_num at hq
    · exact h0
  refine ⟨hqz, ?_, ?_⟩
  · intro hd
    rw [Nat.dvd_iff_mod_eq_zero] at hd
    exact absurd (hd.symm.trans hq) (by norm_num)
  · intro hd
    have hzero : ((q - 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ 3).mpr hd
    rw [Nat.cast_sub hge, Nat.cast_one, hqz] at hzero
    exact absurd hzero (by decide)

private theorem outerFixed3_psl67_aux_rank {n : ℕ} {F : Type} [Field F] [Finite F]
    (hn : n = 6 ∨ n = 7) (hFz : ((Nat.card F : ℕ) : ZMod 3) = 2)
    (hpF : ¬ 3 ∣ Nat.card F) (hdiv : ¬ 3 ∣ Nat.gcd n (Nat.card F - 1))
    (hndvd : ¬ 3 ∣ Nat.card F - 1) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n F))) := by
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hform := pRank_statedProj_SL_formula (F := F) (p := 3) (n := n)
    Nat.prime_three (by norm_num) hn1 hpF hdiv
  rw [if_neg hndvd] at hform
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf ((Nat.card F : ℕ) : ZMod 3) = 2 := by
    rw [hFz]
    exact orderOf_eq_prime (by decide) (by decide)
  rw [hord] at hform
  have hn2 : n / 2 = 3 := by rcases hn with rfl | rfl <;> norm_num
  rw [hform, hn2]

theorem outerFixed3_psl67 {n : ℕ} (hn : n = 6 ∨ n = 7) (hr : r.Prime) (hq : r ^ f % 3 = 2)
    (h : LieModel X .PSL n r f) : OuterFixed3 X := by
  intro ψ hψ hψI
  have hn0 : n ≠ 0 := by rcases hn with rfl | rfl <;> norm_num
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hcl := h.statedClassicalModel_of_ne_zero hn0
  have hcl' := hcl
  obtain ⟨-, F, hF, hFin, hFcard, _⟩ := hcl'
  obtain ⟨hqz, hpq, hndvd0⟩ := outerFixed3_psl67_aux_arith hq
  have hFz : ((Nat.card F : ℕ) : ZMod 3) = 2 := by rw [hFcard]; exact hqz
  have hpF : ¬ 3 ∣ Nat.card F := by rw [hFcard]; exact hpq
  have hndvd : ¬ 3 ∣ Nat.card F - 1 := by rw [hFcard]; exact hndvd0
  have hdiv : ¬ 3 ∣ Nat.gcd n (r ^ f - 1) := fun hd =>
    hndvd0 (hd.trans (Nat.gcd_dvd_right n (r ^ f - 1)))
  have hdiv' : ¬ 3 ∣ Nat.gcd n (Nat.card F - 1) := by rw [hFcard]; exact hdiv
  obtain ⟨hpf, F₀, hF₀, hFin₀, hcard, hrank⟩ :=
    psl_three_pRank_fixed (n := n) hn3 hcl Nat.prime_three (by norm_num) hdiv ψ hψ hψI
  have hcard' : Nat.card F = Nat.card F₀ ^ 3 := by
    rw [hFcard, hcard, ← pow_mul, Nat.div_mul_cancel hpf]
  have heq := pRank_statedProj_SL_eq_of_pow (F := F) (F₀ := F₀) (p := 3) (n := n)
    Nat.prime_three (by norm_num) hn1 hcard' hpF hdiv'
  refine le_trans ?_ hrank
  rw [← heq]
  exact outerFixed3_psl67_aux_rank hn hFz hpF hdiv' hndvd

private theorem outerFixed3_psu4_aux_arith {q : ℕ} (hq : q % 3 = 2) :
    ¬ 3 ∣ q ∧ 3 ∣ q + 1 := by
  have hqz : ((q : ℕ) : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod q 3, hq]
    norm_num
  refine ⟨?_, ?_⟩
  · intro hd
    rw [Nat.dvd_iff_mod_eq_zero] at hd
    exact absurd (hd.symm.trans hq) (by norm_num)
  · rw [← ZMod.natCast_eq_zero_iff]
    rw [Nat.cast_add, Nat.cast_one, hqz]
    decide

private theorem outerFixed3_psu4_aux_rank {F : Type} [Field F] [Finite F] {r f : ℕ}
    (hr : r.Prime) (hq1 : 3 ∣ r ^ f + 1) (hpq : ¬ 3 ∣ r ^ f)
    (hFcard : Nat.card F = (r ^ f) ^ 2) (hdiv : ¬ 3 ∣ Nat.gcd 4 (r ^ f + 1)) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 4 (r ^ f) F))) := by
  have hform := pRank_statedProj_SU_formula (F := F) (p := 3) (ℓ := r) (n := 4) (q := r ^ f)
    Nat.prime_three (by norm_num) hr ⟨f, rfl⟩ (by norm_num) hFcard hpq hdiv
  rw [if_pos hq1] at hform
  rw [hform]

theorem outerFixed3_psu4 (hr : r.Prime) (hq : r ^ f % 3 = 2) (hq2 : r ^ f ≠ 2)
    (h : LieModel X .PSU 4 r f) : OuterFixed3 X := by
  intro ψ hψ hψI
  have hcl := h.statedClassicalModel_of_ne_zero (by norm_num)
  have hcl' := hcl
  obtain ⟨-, F, hF, hFin, hFcard, _⟩ := hcl'
  obtain ⟨hpq, hq1⟩ := outerFixed3_psu4_aux_arith hq
  have hdiv : ¬ 3 ∣ Nat.gcd 4 (r ^ f + 1) := fun hd => by
    have h4 : 3 ∣ 4 := hd.trans (Nat.gcd_dvd_left 4 (r ^ f + 1))
    norm_num at h4
  obtain ⟨hpf, F₀, hF₀, hFin₀, hcard, hrank⟩ :=
    psu_pRank_fixed hcl Nat.prime_three (by norm_num) hdiv (by rintro ⟨h1, -⟩; omega) ψ hψ hψI
  have hqeq : r ^ f = (r ^ (f / 3)) ^ 3 := by
    rw [← pow_mul, Nat.div_mul_cancel hpf]
  have heq := pRank_statedProj_SU_eq_of_pow (F := F) (F₀ := F₀) (p := 3) (n := 4)
    (q := r ^ f) (q₀ := r ^ (f / 3)) Nat.prime_three (by norm_num) hr ⟨f, rfl⟩
    ⟨f / 3, rfl⟩ (by norm_num) hFcard hcard hqeq hpq hdiv
  refine le_trans ?_ hrank
  rw [← heq]
  exact outerFixed3_psu4_aux_rank hr hq1 hpq hFcard hdiv

private theorem outerFixed3_psu67_aux_arith {q : ℕ} (hq : q % 3 = 1) :
    ((q : ℕ) : ZMod 3) = 1 ∧ ¬ 3 ∣ q ∧ ¬ 3 ∣ q + 1 := by
  have hqz : ((q : ℕ) : ZMod 3) = 1 := by
    rw [← ZMod.natCast_mod q 3, hq]
    norm_num
  refine ⟨hqz, ?_, ?_⟩
  · intro hd
    rw [Nat.dvd_iff_mod_eq_zero] at hd
    exact absurd (hd.symm.trans hq) (by norm_num)
  · intro hd
    have hzero : ((q + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ 3).mpr hd
    rw [Nat.cast_add, Nat.cast_one, hqz] at hzero
    exact absurd hzero (by decide)

private theorem outerFixed3_psu67_aux_rank {n : ℕ} {F : Type} [Field F] [Finite F] {r f : ℕ}
    (hn : n = 6 ∨ n = 7) (hr : r.Prime) (hqz : ((r ^ f : ℕ) : ZMod 3) = 1)
    (hpq : ¬ 3 ∣ r ^ f) (hFcard : Nat.card F = (r ^ f) ^ 2)
    (hdiv : ¬ 3 ∣ Nat.gcd n (r ^ f + 1)) (hq1 : ¬ 3 ∣ r ^ f + 1) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (r ^ f) F))) := by
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hform := pRank_statedProj_SU_formula (F := F) (p := 3) (ℓ := r) (n := n) (q := r ^ f)
    Nat.prime_three (by norm_num) hr ⟨f, rfl⟩ hn1 hFcard hpq hdiv
  rw [if_neg hq1] at hform
  have hord : orderOf (-(((r ^ f : ℕ)) : ZMod 3)) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hneg : (-(((r ^ f : ℕ)) : ZMod 3)) = 2 := by rw [hqz]; decide
    rw [hneg]
    exact orderOf_eq_prime (by decide) (by decide)
  have hn2 : n / 2 = 3 := by rcases hn with rfl | rfl <;> norm_num
  have hform' : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (r ^ f) F))) = 3 :=
    hform.trans ((congrArg (fun k => n / k) hord).trans hn2)
  rw [hform']

theorem outerFixed3_psu67 {n : ℕ} (hn : n = 6 ∨ n = 7) (hr : r.Prime) (hq : r ^ f % 3 = 1)
    (h : LieModel X .PSU n r f) : OuterFixed3 X := by
  intro ψ hψ hψI
  have hn0 : n ≠ 0 := by rcases hn with rfl | rfl <;> norm_num
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hcl := h.statedClassicalModel_of_ne_zero hn0
  have hcl' := hcl
  obtain ⟨-, F, hF, hFin, hFcard, _⟩ := hcl'
  obtain ⟨hqz, hpq, hq1⟩ := outerFixed3_psu67_aux_arith hq
  have hdiv : ¬ 3 ∣ Nat.gcd n (r ^ f + 1) := fun hd =>
    hq1 (hd.trans (Nat.gcd_dvd_right n (r ^ f + 1)))
  obtain ⟨hpf, F₀, hF₀, hFin₀, hcard, hrank⟩ :=
    psu_pRank_fixed hcl Nat.prime_three (by norm_num) hdiv
      (by rintro ⟨h1, -⟩; rcases hn with rfl | rfl <;> omega) ψ hψ hψI
  have hqeq : r ^ f = (r ^ (f / 3)) ^ 3 := by
    rw [← pow_mul, Nat.div_mul_cancel hpf]
  have heq := pRank_statedProj_SU_eq_of_pow (F := F) (F₀ := F₀) (p := 3) (n := n)
    (q := r ^ f) (q₀ := r ^ (f / 3)) Nat.prime_three (by norm_num) hr ⟨f, rfl⟩
    ⟨f / 3, rfl⟩ hn1 hFcard hcard hqeq hpq hdiv
  refine le_trans ?_ hrank
  rw [← heq]
  exact outerFixed3_psu67_aux_rank hn hr hqz hpq hFcard hdiv hq1

theorem outerFixed3_of_isLieFam811 {fam : LieFam811} (h : IsLieFam811 X fam r f) :
    OuterFixed3 X := by
  cases fam with
  | psp6 => exact outerFixed3_psp6 h.1 h.2.1 h.2.2
  | omega7 => exact outerFixed3_omega7 h.1 h.2.1 h.2.2.1 h.2.2.2
  | pomega8m => exact outerFixed3_pomega8m h.1 h.2.1 h.2.2
  | l4 =>
    obtain ⟨hr, hq2, ⟨hq, hm⟩ | ⟨hq, hm⟩⟩ := h
    · exact outerFixed3_psl4 hr hq hm
    · exact outerFixed3_psu4 hr hq hq2 hm
  | l6 =>
    obtain ⟨hr, ⟨hq, hm⟩ | ⟨hq, hm⟩⟩ := h
    · exact outerFixed3_psl67 (Or.inl rfl) hr hq hm
    · exact outerFixed3_psu67 (Or.inl rfl) hr hq hm
  | l7 =>
    obtain ⟨hr, ⟨hq, hm⟩ | ⟨hq, hm⟩⟩ := h
    · exact outerFixed3_psl67 (Or.inr rfl) hr hq hm
    · exact outerFixed3_psu67 (Or.inr rfl) hr hq hm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
