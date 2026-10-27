module

public import CFSG.Permutation.UnitaryThreeRecognition.DThreeCore
public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgMoufang

public section

namespace CFSG.UnitaryThreeRecognition.DThree

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

variable (J) in
structure SMapHyp3 (q : ℕ) (F : Coord J → Coord J) (σ : Kˣ → Kˣ) (h : Coord J → Kˣ) :
    Prop where
  card : Nat.card K = q ^ 2
  conj_pow : ∀ x, J.conj x = x ^ q
  q_odd : Odd q
  q_ge : 5 ≤ q
  three_dvd : 3 ∣ q + 1
  F_ne : ∀ c, c ≠ 1 → F c ≠ 1
  F_F : ∀ c, c ≠ 1 → F (F c) = c
  F_torus : ∀ (k : Kˣ) (c : Coord J), c ≠ 1 →
    F (hermitianTorusAction J k c) = hermitianTorusAction J (σ k) (F c)
  σ_mul : ∀ (k k' : Kˣ) (c : Coord J),
    hermitianTorusAction J (σ (k * k')) c = hermitianTorusAction J (σ k * σ k') c
  σ_fix : ∀ k : Kˣ, (∀ c : Coord J, hermitianTorusAction J (σ k) c = hermitianTorusAction J k c) →
    (k : K) * J.conj (k : K) = 1
  σ_step0 : ∀ (k : Kˣ) (c : Coord J), hermitianTorusAction J ((σ k * k ^ q) ^ 2) c = c
  F_Z : ∀ c : Coord J, c ≠ 1 → c.1.1 = 0 → (F c).1.1 = 0
  F_moufang : ∀ u v : Coord J, u ≠ 1 → v ≠ 1 → u * F v ≠ 1 → (F u⁻¹)⁻¹ * v ≠ 1 →
    F (u * F v) = F u * hermitianTorusAction J (h u) (F ((F u⁻¹)⁻¹ * v))
  h_rel : ∀ u : Coord J, u ≠ 1 → hermitianTorusAction J (h u) (F (F u⁻¹)⁻¹) = (F u)⁻¹
  h_torus : ∀ (k : Kˣ) (u c : Coord J), u ≠ 1 →
    hermitianTorusAction J (h (hermitianTorusAction J k u)) c =
      hermitianTorusAction J (σ k * h u * k⁻¹) c
  fix_tor : ∀ u : Coord J, u ≠ 1 → F u = u → ∀ c : Coord J,
    hermitianTorusAction J (h u) c = hermitianTorusAction J (-1) c
  fix_inv : ∀ u : Coord J, u ≠ 1 → F u = u → hermitianTorusAction J (-1) (F u⁻¹)⁻¹ = F u⁻¹
  fix_exists : ∃ u : Coord J, u ≠ 1 ∧ F u = u

theorem exists_fst_one (h2 : (2 : K) ≠ 0) : ∃ w : Coord J, w.1.1 = 1 := by
  refine ⟨⟨(1, -1 / 2), ?_⟩, rfl⟩
  show (-1 / 2 : K) + J.conj (-1 / 2) + 1 * J.conj 1 = 0
  rw [map_div₀, map_neg, map_one, map_ofNat]
  field_simp; ring

theorem t_eq_one_iff (h2 : (2 : K) ≠ 0) {z₀ : Coord J} (hz₀ : z₀ ≠ 1)
    {q : ℕ} (hconj : ∀ x, J.conj x = x ^ q) (h3 : 3 ∣ q + 1) (m : Kˣ) :
    (∀ c : Coord J, hermitianTorusAction J m c = c) ↔ (m : K) ^ 3 = 1 := by
  have hm := m.ne_zero
  have hcm : J.conj (m : K) ≠ 0 := (map_ne_zero J.conj).2 hm
  constructor
  · intro hk
    have hN : (m : K) * J.conj (m : K) = 1 := by
      have e := congrArg (fun v : Coord J => v.1.2) (hk z₀)
      change (hermitianTorusAction J m z₀).1.2 = z₀.1.2 at e
      rw [torus_snd] at e
      have hb := coord_snd_ne_zero J hz₀
      field_simp at e
      linear_combination -e
    obtain ⟨w, hw⟩ := exists_fst_one (J := J) h2
    have e := congrArg (fun v : Coord J => v.1.1) (hk w)
    change (hermitianTorusAction J m w).1.1 = w.1.1 at e
    rw [torus_fst, hw] at e
    have hcm' : J.conj (m : K) = (m : K)⁻¹ := eq_inv_of_mul_eq_one_right hN
    rw [hcm', inv_inv] at e
    linear_combination e
  · intro h3m c
    have hq : (m : K) ^ (q + 1) = 1 := by
      obtain ⟨r, hr⟩ := h3
      rw [hr, pow_mul, h3m, one_pow]
    have hcm' : J.conj (m : K) = (m : K)⁻¹ := by
      rw [hconj]; exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hq)
    apply coord_ext
    · rw [torus_fst, hcm', inv_inv]
      linear_combination c.1.1 * h3m
    · rw [torus_snd, hcm', inv_inv]
      field_simp

variable {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ → Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp3

variable (H : SMapHyp3 J q F σ h)
include H

theorem finite : Finite K := by
  apply Nat.finite_of_card_ne_zero
  rw [H.card]; have := H.q_ge; positivity

theorem two_ne : (2 : K) ≠ 0 := by
  classical
  intro h2
  have := H.finite
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 := by
    have := ringChar.dvd (show ((2 : ℕ) : K) = 0 by exact_mod_cast h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h | h
    · exact absurd h (CharP.ringChar_ne_one)
    · exact h
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, H.card, hchar] at hn
  have hev : Even (q ^ 2) := by rw [hn]; exact (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)
  exact (Nat.not_even_iff_odd.mpr (H.q_odd.pow)) hev

theorem three_ne : (3 : K) ≠ 0 := by
  classical
  intro h3
  have := H.finite
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 3 := by
    have := ringChar.dvd (show ((3 : ℕ) : K) = 0 by exact_mod_cast h3)
    rcases (Nat.dvd_prime Nat.prime_three).mp this with h | h
    · exact absurd h (CharP.ringChar_ne_one)
    · exact h
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, H.card, hchar] at hn
  have h3q : 3 ∣ q ^ 2 := by rw [hn]; exact dvd_pow_self 3 n.ne_zero
  have h3q' : 3 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3q
  have := H.three_dvd
  omega

theorem exists_trace_zero : ∃ c : K, c ≠ 0 ∧ J.conj c = -c := by
  classical
  have := H.finite
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hq := H.q_ge
  have hog : orderOf g = q * q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units, ← Nat.card_eq_fintype_card, H.card, sq]
  have hne : J.conj (g : K) ≠ g := by
    intro e
    rw [H.conj_pow] at e
    have h1 : g ^ (q - 1) = 1 := by
      apply Units.ext
      have h2 : (g : K) ^ (q - 1) * g = g := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), e]
      simpa using (mul_eq_right₀ g.ne_zero).mp h2
    have h3 := orderOf_le_of_pow_eq_one (by omega) h1
    rw [hog] at h3
    have : q ≤ q * q - q := by
      have : 3 * q ≤ q * q := Nat.mul_le_mul_right q (by omega)
      omega
    omega
  refine ⟨(g : K) - J.conj g, sub_ne_zero.mpr (Ne.symm hne), ?_⟩
  rw [map_sub, conj_conj]; ring

theorem exists_central : ∃ z : Coord J, z ≠ 1 ∧ z.1.1 = 0 := by
  obtain ⟨c, hc0, hc⟩ := H.exists_trace_zero
  exact ⟨zc c hc, fun e => hc0 (congrArg (fun v : Coord J => v.1.2) e), rfl⟩

theorem t_triv_iff (m : Kˣ) :
    (∀ c : Coord J, hermitianTorusAction J m c = c) ↔ (m : K) ^ 3 = 1 := by
  obtain ⟨z₀, hz₀, -⟩ := H.exists_central
  exact t_eq_one_iff H.two_ne hz₀ H.conj_pow H.three_dvd m

theorem t_eq_iff (m m' : Kˣ) :
    (∀ c : Coord J, hermitianTorusAction J m c = hermitianTorusAction J m' c) ↔
      ((m : K) / m') ^ 3 = 1 := by
  have hm' := m'.ne_zero
  rw [show ((m : K) / m') = ((m * m'⁻¹ : Kˣ) : K) by simp [div_eq_mul_inv], ← H.t_triv_iff]
  constructor
  · intro hk c
    rw [torus_mul_apply, hk, ← torus_mul_apply, mul_inv_cancel, torus_one_apply]
  · intro hk c
    have e : m = m' * (m * m'⁻¹) := by rw [mul_comm m m'⁻¹, mul_inv_cancel_left]
    rw [e, torus_mul_apply, hk]

theorem cj_eq_pow (k : Kˣ) : cj J k = k ^ q := Units.ext (by rw [cj_val, H.conj_pow]; simp)

@[expose] noncomputable def sgn (σ : Kˣ → Kˣ) (k : Kˣ) : K := ((σ k : K) * J.conj (k : K)) ^ 3

omit H in
theorem sgn_def (k : Kˣ) : sgn (J := J) σ k = ((σ k : K) * J.conj (k : K)) ^ 3 := rfl

theorem sgn_sq (k : Kˣ) : sgn (J := J) σ k ^ 2 = 1 := by
  have h0 := (H.t_triv_iff ((σ k * k ^ q) ^ 2)).mp (H.σ_step0 k)
  rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_pow_eq_pow_val, ← H.conj_pow] at h0
  rw [sgn_def]
  linear_combination h0

theorem sgn_eq (k : Kˣ) : sgn (J := J) σ k = 1 ∨ sgn (J := J) σ k = -1 := by
  have := H.sgn_sq k
  have : (sgn (J := J) σ k - 1) * (sgn (J := J) σ k + 1) = 0 := by linear_combination this
  rcases mul_eq_zero.mp this with h | h
  · left; linear_combination h
  · right; linear_combination h

theorem t_sigma (k : Kˣ) (c : Coord J) :
    hermitianTorusAction J (σ k) c =
      hermitianTorusAction J (Units.mk0 (sgn (J := J) σ k) (by
        rcases H.sgn_eq k with e | e <;> rw [e] <;> norm_num) * (cj J k)⁻¹) c := by
  have hk := k.ne_zero
  have hck : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  revert c
  rw [H.t_eq_iff]
  rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, cj_val]
  have e' : ((σ k : K) * J.conj (k : K)) ^ 3 = sgn (J := J) σ k := rfl
  rcases H.sgn_eq k with e | e
  · rw [e]; rw [e] at e'; field_simp; linear_combination e'
  · rw [e]; rw [e] at e'; field_simp; linear_combination -e'

theorem sgn_mul (k k' : Kˣ) :
    sgn (J := J) σ (k * k') = sgn (J := J) σ k * sgn (J := J) σ k' := by
  have hm := (H.t_eq_iff (σ (k * k')) (σ k * σ k')).mp (H.σ_mul k k')
  have hne : ((σ k * σ k' : Kˣ) : K) ≠ 0 := Units.ne_zero _
  rw [div_pow] at hm
  have h1 : ((σ (k * k') : Kˣ) : K) ^ 3 = ((σ k * σ k' : Kˣ) : K) ^ 3 := by
    rw [div_eq_one_iff_eq (pow_ne_zero _ hne)] at hm; exact hm
  rw [sgn_def, sgn_def, sgn_def, mul_pow, h1, Units.val_mul, Units.val_mul, map_mul]
  ring

theorem sgn_mul_self (k : Kˣ) : sgn (J := J) σ (k * k) = 1 := by
  rw [H.sgn_mul, ← sq, H.sgn_sq]

theorem sgn_eq_one_of_conj {k : Kˣ} (hk : J.conj (k : K) = k) : sgn (J := J) σ k = 1 := by
  classical
  have := H.finite
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    intro e
    apply H.two_ne
    have := ringChar.spec K 2
    rw [e] at this
    exact_mod_cast (this.mpr (dvd_refl 2))
  have hsq : IsSquare (k : K) := by
    rw [FiniteField.isSquare_iff hchar k.ne_zero, ← Nat.card_eq_fintype_card, H.card]
    have hq1 : (k : K) ^ q = k := by rw [← H.conj_pow, hk]
    have hk1 : (k : K) ^ (q - 1) = 1 := by
      have hq := H.q_ge
      have : (k : K) ^ (q - 1) * k = k := by rw [← pow_succ, Nat.sub_add_cancel (by omega), hq1]
      exact (mul_eq_right₀ k.ne_zero).mp this
    obtain ⟨r, hr⟩ := H.q_odd
    have : q ^ 2 / 2 = (q - 1) * (r + 1) := by
      subst hr
      have : (2 * r + 1) ^ 2 = 2 * ((2 * r + 1 - 1) * (r + 1)) + 1 := by
        rw [show 2 * r + 1 - 1 = 2 * r by omega]; ring
      omega
    rw [this, pow_mul, hk1, one_pow]
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero] at hr; exact k.ne_zero hr
  have hkr : k = Units.mk0 r hr0 * Units.mk0 r hr0 := Units.ext (by simp [hr])
  rw [hkr, H.sgn_mul_self]

end SMapHyp3

end CFSG.UnitaryThreeRecognition.DThree
