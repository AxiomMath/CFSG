module

public import CFSG.Permutation.UnitaryThreeRecognition.DThreeSign

public section

namespace CFSG.UnitaryThreeRecognition.DThree

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

variable {K : Type*} [Field K] {J : HermitianForm 3 K}
variable {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ → Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp3

variable (H : SMapHyp3 J q F σ h)
include H

theorem sgn_ne (k : Kˣ) : sgn (J := J) σ k ≠ 0 := by
  rcases H.sgn_eq k with e | e <;> rw [e] <;> norm_num

theorem conj_sgn (k : Kˣ) : J.conj (sgn (J := J) σ k) = sgn (J := J) σ k := by
  rcases H.sgn_eq k with e | e <;> rw [e] <;> simp

theorem sgn_mul_sgn (k : Kˣ) : sgn (J := J) σ k * sgn (J := J) σ k = 1 := by
  rw [← sq, H.sgn_sq]

theorem t_sigma_snd (k : Kˣ) (X : Coord J) :
    (hermitianTorusAction J (σ k) X).1.2 = X.1.2 * ((k : K) * J.conj (k : K)) := by
  have hk := k.ne_zero
  have hck : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  have hs := H.sgn_ne k
  rw [H.t_sigma k X, torus_snd, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, cj_val,
    map_mul, map_inv₀, conj_conj, H.conj_sgn]
  rcases H.sgn_eq k with e | e <;> rw [e] <;> field_simp

theorem t_sigma_fst (k : Kˣ) (X : Coord J) :
    (hermitianTorusAction J (σ k) X).1.1 =
      sgn (J := J) σ k * (X.1.1 * (J.conj (k : K))⁻¹ * (k : K) ^ 2) := by
  have hk := k.ne_zero
  have hck : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  have hs := H.sgn_ne k
  rw [H.t_sigma k X, torus_fst, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, cj_val,
    map_mul, map_inv₀, conj_conj, H.conj_sgn]
  rcases H.sgn_eq k with e | e <;> rw [e] <;> field_simp

theorem exists_F_center : ∃ κ : K, κ ≠ 0 ∧ J.conj κ = κ ∧
    ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 → (F z).1.1 = 0 ∧ (F z).1.2 * z.1.2 = κ := by
  have := H.finite
  obtain ⟨c₁, hc₁, hcc₁⟩ := H.exists_trace_zero
  set z₁ : Coord J := zc c₁ hcc₁ with hz₁def
  have hz₁ : z₁ ≠ 1 := fun e => hc₁ (congrArg (fun v : Coord J => v.1.2) e)
  have hF₁ : (F z₁).1.1 = 0 := H.F_Z z₁ hz₁ rfl
  set M₁ := (F z₁).1.2 with hM₁def
  have hM₁ : M₁ ≠ 0 := coord_snd_ne_zero J (H.F_ne z₁ hz₁)
  have hcM₁ : J.conj M₁ = -M₁ := conj_snd_of_fst_eq_zero hF₁
  refine ⟨M₁ * c₁, mul_ne_zero hM₁ hc₁, by rw [map_mul, hcM₁, hcc₁]; ring, ?_⟩
  intro z hz hz0
  refine ⟨H.F_Z z hz hz0, ?_⟩
  have hc : z.1.2 ≠ 0 := coord_snd_ne_zero J hz
  have hcc : J.conj z.1.2 = -z.1.2 := conj_snd_of_fst_eq_zero hz0
  have hx : c₁ / z.1.2 ≠ 0 := div_ne_zero hc₁ hc
  have hxc : J.conj (c₁ / z.1.2) = c₁ / z.1.2 := by rw [map_div₀, hcc₁, hcc, neg_div_neg_eq]
  obtain ⟨k, hk⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hx hxc
  have hk' : (k : K) * J.conj (k : K) = c₁ / z.1.2 := hk
  have hkz : hermitianTorusAction J k z₁ = z := by
    apply coord_ext
    · rw [torus_fst, hz0]; change 0 * (k : K) * _ = 0; ring
    · rw [torus_snd]
      change c₁ * (J.conj (k : K))⁻¹ * (k : K)⁻¹ = z.1.2
      rw [mul_assoc, ← mul_inv, mul_comm (J.conj _), hk']
      field_simp
  rw [← hkz, H.F_torus k z₁ hz₁, H.t_sigma_snd, ← hM₁def, hk', hkz]
  field_simp

theorem isSquare_of_conj {x : K} (hx : x ≠ 0) (hxc : J.conj x = x) : IsSquare x := by
  classical
  have := H.finite
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    intro e
    apply H.two_ne
    have := ringChar.spec K 2
    rw [e] at this
    exact_mod_cast (this.mpr (dvd_refl 2))
  rw [FiniteField.isSquare_iff hchar hx, ← Nat.card_eq_fintype_card, H.card]
  have hq1 : x ^ q = x := by rw [← H.conj_pow, hxc]
  have hk1 : x ^ (q - 1) = 1 := by
    have hq := H.q_ge
    have : x ^ (q - 1) * x = x := by rw [← pow_succ, Nat.sub_add_cancel (by omega), hq1]
    exact (mul_eq_right₀ hx).mp this
  obtain ⟨r, hr⟩ := H.q_odd
  have : q ^ 2 / 2 = (q - 1) * (r + 1) := by
    subst hr
    have : (2 * r + 1) ^ 2 = 2 * ((2 * r + 1 - 1) * (r + 1)) + 1 := by
      rw [show 2 * r + 1 - 1 = 2 * r by omega]; ring
    omega
  rw [this, pow_mul, hk1, one_pow]

theorem sqrt_dichotomy {x : K} (hx : x ≠ 0) (hxc : J.conj x = x) :
    ∃ r : K, r ≠ 0 ∧ r * r = x ∧ (J.conj r = r ∨ J.conj r = -r) := by
  obtain ⟨r, hr⟩ := H.isSquare_of_conj hx hxc
  have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero] at hr; exact hx hr
  refine ⟨r, hr0, hr.symm, ?_⟩
  have e : J.conj r * J.conj r = r * r := by rw [← map_mul, ← hr, hxc]
  have : (J.conj r - r) * (J.conj r + r) = 0 := by linear_combination e
  rcases mul_eq_zero.mp this with h | h
  · left; linear_combination h
  · right; linear_combination h

theorem exists_sqrt_kappa {κ : K} (hκ0 : κ ≠ 0) (hκc : J.conj κ = κ)
    (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 → (F z).1.1 = 0 ∧ (F z).1.2 * z.1.2 = κ) :
    ∃ l : K, l ≠ 0 ∧ J.conj l = l ∧ l * l = κ := by
  have h2 := H.two_ne
  obtain ⟨r, hr0, hrr, hrc | hrc⟩ := H.sqrt_dichotomy hκ0 hκc
  · exact ⟨r, hr0, hrc, hrr⟩
  · exfalso
    set z : Coord J := zc r hrc with hzdef
    have hz : z ≠ 1 := fun e => hr0 (congrArg (fun v : Coord J => v.1.2) e)
    have hz0 : z.1.1 = 0 := rfl
    obtain ⟨hFz1, hFz2⟩ := hκF z hz hz0
    have hFz : F z = z := by
      apply coord_ext
      · rw [hFz1, hz0]
      · change (F z).1.2 = r
        change (F z).1.2 * r = κ at hFz2
        rw [← hrr] at hFz2
        exact mul_right_cancel₀ hr0 (hFz2.trans (by ring))
    have hzi : z⁻¹ ≠ 1 := inv_ne_one.mpr hz
    obtain ⟨hFi1, hFi2⟩ := hκF z⁻¹ hzi (by rw [inv_fst, hz0, neg_zero])
    have hFzi : F z⁻¹ = z⁻¹ := by
      apply coord_ext
      · rw [hFi1, inv_fst, hz0, neg_zero]
      · rw [inv_snd] at hFi2 ⊢
        change (F z⁻¹).1.2 * J.conj r = κ at hFi2
        change (F z⁻¹).1.2 = J.conj r
        rw [hrc] at hFi2 ⊢
        rw [← hrr] at hFi2
        have : ((F z⁻¹).1.2 + r) * r = 0 := by linear_combination -hFi2
        linear_combination (mul_eq_zero.mp this).resolve_right hr0
    have hrel := H.h_rel z hz
    rw [hFzi, inv_inv, hFz, H.fix_tor z hz hFz] at hrel
    have := congrArg (fun v : Coord J => v.1.2) hrel
    simp only [jm_snd, inv_snd] at this
    change r = J.conj r at this
    rw [hrc] at this
    exact hr0 (by
      have : 2 * r = 0 := by linear_combination this
      exact (mul_eq_zero.mp this).resolve_left h2)

theorem no_central_fix {κ : K} (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 →
    (F z).1.1 = 0 ∧ (F z).1.2 * z.1.2 = κ) {z : Coord J} (hz : z ≠ 1) (hz0 : z.1.1 = 0) :
    F z ≠ z := by
  intro hFz
  have h2 := H.two_ne
  have hc := coord_snd_ne_zero J hz
  have hcc : J.conj z.1.2 = -z.1.2 := conj_snd_of_fst_eq_zero hz0
  have hzi : z⁻¹ ≠ 1 := inv_ne_one.mpr hz
  have hzi0 : z⁻¹.1.1 = 0 := by rw [inv_fst, hz0, neg_zero]
  have hκ : κ = z.1.2 * z.1.2 := by
    have := (hκF z hz hz0).2; rw [hFz] at this; exact this.symm
  have hFzi : F z⁻¹ = z⁻¹ := by
    apply coord_ext
    · rw [(hκF z⁻¹ hzi hzi0).1, inv_fst, hz0, neg_zero]
    · have e := (hκF z⁻¹ hzi hzi0).2
      rw [inv_snd, hcc, hκ] at e
      rw [inv_snd, hcc]
      have : ((F z⁻¹).1.2 + z.1.2) * z.1.2 = 0 := by linear_combination -e
      linear_combination (mul_eq_zero.mp this).resolve_right hc
  have hrel := H.h_rel z hz
  rw [hFzi, inv_inv, hFz, H.fix_tor z hz hFz] at hrel
  have := congrArg (fun v : Coord J => v.1.2) hrel
  simp only [jm_snd, inv_snd] at this
  rw [hcc] at this
  exact hc (by
    have : 2 * z.1.2 = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left h2)

theorem fix_exists' : ∃ u : Coord J, u.1.1 ≠ 0 ∧ F u = u := by
  obtain ⟨κ, -, -, hκF⟩ := H.exists_F_center
  obtain ⟨u, hu, hFu⟩ := H.fix_exists
  refine ⟨u, fun h0 => H.no_central_fix hκF hu h0 hFu, hFu⟩

end SMapHyp3

end CFSG.UnitaryThreeRecognition.DThree
