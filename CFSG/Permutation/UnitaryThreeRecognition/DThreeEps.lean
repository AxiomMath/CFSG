module

public import CFSG.Permutation.UnitaryThreeRecognition.DThreeKappa

public section

namespace CFSG.UnitaryThreeRecognition.DThree

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

theorem cube_of_fix {X : Coord J} (hX : X.1.1 ≠ 0) {m : Kˣ}
    (hm : hermitianTorusAction J m X = X) : (m : K) ^ 3 = 1 := by
  have hm0 := m.ne_zero
  have hcm : J.conj (m : K) ≠ 0 := (map_ne_zero J.conj).2 hm0
  have hX1 : X ≠ 1 := ne_one_of_fst hX
  have hb := coord_snd_ne_zero J hX1
  have e1 := congrArg (fun v : Coord J => v.1.1) hm
  have e2 := congrArg (fun v : Coord J => v.1.2) hm
  simp only [torus_fst, torus_snd] at e1 e2
  have hN : (m : K) * J.conj (m : K) = 1 := by field_simp at e2; linear_combination -e2
  have hcm' : J.conj (m : K) = (m : K)⁻¹ := eq_inv_of_mul_eq_one_right hN
  rw [hcm', inv_inv] at e1
  have : X.1.1 * ((m : K) ^ 3 - 1) = 0 := by linear_combination e1
  linear_combination (mul_eq_zero.mp this).resolve_left hX

variable {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ → Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp3

variable (H : SMapHyp3 J q F σ h)
include H

omit H in
theorem F_zc {κ : K} (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 →
    (F z).1.1 = 0 ∧ (F z).1.2 * z.1.2 = κ) {z : Coord J} (hz : z ≠ 1) (hz0 : z.1.1 = 0) :
    (F z).1.2 = κ / z.1.2 := by
  have hc := coord_snd_ne_zero J hz
  rw [eq_div_iff hc]; exact (hκF z hz hz0).2

omit H in
theorem F_inv_inv_center {κ : K} (hκc : J.conj κ = κ) (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 →
    (F z).1.1 = 0 ∧ (F z).1.2 * z.1.2 = κ) {z : Coord J} (hz : z ≠ 1) (hz0 : z.1.1 = 0) :
    (F z⁻¹)⁻¹ = F z := by
  have hzi : z⁻¹ ≠ 1 := inv_ne_one.mpr hz
  have hzi0 : z⁻¹.1.1 = 0 := by rw [inv_fst, hz0, neg_zero]
  have hc := coord_snd_ne_zero J hz
  have hcc : J.conj z.1.2 = -z.1.2 := conj_snd_of_fst_eq_zero hz0
  apply coord_ext
  · rw [inv_fst, (hκF _ hzi hzi0).1, (hκF z hz hz0).1, neg_zero]
  · rw [inv_snd, F_zc hκF hzi hzi0, F_zc hκF hz hz0, inv_snd, map_div₀, hκc, conj_conj]

theorem zm_twice {κ : K} (hκc : J.conj κ = κ) (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 →
    (F z).1.1 = 0 ∧ (F z).1.2 * z.1.2 = κ) {w : Coord J} (hw : w.1.1 ≠ 0) (hFw : F w = w)
    {z : Coord J} (hz : z ≠ 1) (hz0 : z.1.1 = 0) :
    ((h z : K) * h (F z)) ^ 3 = 1 := by
  have hw1 : w ≠ 1 := ne_one_of_fst hw
  have hFz1 : F z ≠ 1 := H.F_ne z hz
  have hFz0 : (F z).1.1 = 0 := (hκF z hz hz0).1
  have hFFz : F (F z) = z := H.F_F z hz
  have hrz := F_inv_inv_center hκc hκF hz hz0
  have hrz' := F_inv_inv_center hκc hκF hFz1 hFz0
  rw [hFFz] at hrz'
  have hzw : (z * w).1.1 ≠ 0 := by rw [central_comm hz0, mul_central_fst _ hz0]; exact hw
  have hFzw : (F z * w).1.1 ≠ 0 := by rw [central_comm hFz0, mul_central_fst _ hFz0]; exact hw
  have hne1 : z * F w ≠ 1 := by rw [hFw]; exact ne_one_of_fst hzw
  have hne2 : (F z⁻¹)⁻¹ * w ≠ 1 := by rw [hrz]; exact ne_one_of_fst hFzw
  have hne3 : F z * F w ≠ 1 := by rw [hFw]; exact ne_one_of_fst hFzw
  have hne4 : (F (F z)⁻¹)⁻¹ * w ≠ 1 := by rw [hrz']; exact ne_one_of_fst hzw
  have e1 := H.F_moufang z w hz hw1 hne1 hne2
  have e2 := H.F_moufang (F z) w hFz1 hw1 hne3 hne4
  rw [hFw, hrz] at e1
  rw [hFw, hrz', hFFz] at e2
  have hrel := H.h_rel z hz
  rw [hrz, hFFz] at hrel
  rw [e2, torus_mul_hom, hrel, ← mul_assoc, mul_inv_cancel, one_mul, ← torus_mul_apply] at e1
  have hX : (F (z * w)).1.1 ≠ 0 := by
    intro h0
    have hc : F (z * w) ≠ 1 := H.F_ne _ (ne_one_of_fst hzw)
    have := (hκF _ hc h0).1
    rw [H.F_F _ (ne_one_of_fst hzw)] at this
    exact hzw this
  have := cube_of_fix hX e1.symm
  rw [Units.val_mul] at this
  exact this

theorem nrm_h_center {κ : K} (hκc : J.conj κ = κ)
    (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 → (F z).1.1 = 0 ∧ (F z).1.2 * z.1.2 = κ)
    {z : Coord J} (hz : z ≠ 1) (hz0 : z.1.1 = 0) :
    (h z : K) * J.conj (h z : K) * κ = -(z.1.2 ^ 2) := by
  have hrel := H.h_rel z hz
  rw [F_inv_inv_center hκc hκF hz hz0, H.F_F z hz] at hrel
  have e := congrArg (fun v : Coord J => v.1.2) hrel
  simp only [torus_snd, inv_snd] at e
  have hc := coord_snd_ne_zero J hz
  have hh := (h z).ne_zero
  have hch : J.conj (h z : K) ≠ 0 := (map_ne_zero J.conj).2 hh
  rw [F_zc hκF hz hz0, map_div₀, hκc, conj_snd_of_fst_eq_zero hz0] at e
  field_simp at e
  linear_combination e

theorem h_center_torus (k : Kˣ) {z : Coord J} (hz : z ≠ 1) :
    ((h (hermitianTorusAction J k z) : K) /
      (sgn (J := J) σ k * (h z : K) / ((k : K) * J.conj (k : K)))) ^ 3 = 1 := by
  have hk := k.ne_zero
  have hck : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  have hs := H.sgn_ne k
  have h1 := (H.t_eq_iff _ _).mp (H.h_torus k z · hz)
  have h2 := (H.t_eq_iff _ _).mp (H.t_sigma k)
  rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val] at h1
  rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, cj_val] at h2
  have hσ := (σ k).ne_zero
  have hh := (h z).ne_zero
  have e : (h (hermitianTorusAction J k z) : K) /
      (sgn (J := J) σ k * (h z : K) / ((k : K) * J.conj (k : K))) =
      ((h (hermitianTorusAction J k z) : K) / ((σ k : K) * (h z : K) * (k : K)⁻¹)) *
        ((σ k : K) / (sgn (J := J) σ k * (J.conj (k : K))⁻¹)) := by
    field_simp
  rw [e, mul_pow, h1, h2, one_mul]

theorem ringChar_ne_two [Fintype K] : ringChar K ≠ 2 := by
  intro e
  apply H.two_ne
  have := ringChar.spec K 2
  rw [e] at this
  exact_mod_cast (this.mpr (dvd_refl 2))

theorem isSquare_mul_of_not {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxs : ¬IsSquare x)
    (hys : ¬IsSquare y) : IsSquare (x * y) := by
  classical
  have := H.finite
  have : Fintype K := Fintype.ofFinite K
  have hc := H.ringChar_ne_two
  rw [FiniteField.isSquare_iff hc (mul_ne_zero hx hy), mul_pow]
  rw [FiniteField.isSquare_iff hc hx] at hxs
  rw [FiniteField.isSquare_iff hc hy] at hys
  rw [(FiniteField.pow_dichotomy hc hx).resolve_left hxs,
    (FiniteField.pow_dichotomy hc hy).resolve_left hys]
  ring

theorem sgn_of_isSquare {m : Kˣ} (hm : IsSquare (m : K)) : sgn (J := J) σ m = 1 := by
  obtain ⟨r, hr⟩ := hm
  have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero] at hr; exact m.ne_zero hr
  have : m = Units.mk0 r hr0 * Units.mk0 r hr0 := Units.ext (by simp [hr])
  rw [this, H.sgn_mul_self]

omit H in
theorem not_isSquare_of_nrm {m : Kˣ}
    (hm : ∀ r : K, J.conj r = r → r * r ≠ (m : K) * J.conj (m : K)) : ¬IsSquare (m : K) := by
  rintro ⟨r, hr⟩
  apply hm (r * J.conj r) (by rw [map_mul, conj_conj, mul_comm])
  rw [hr, map_mul]; ring

theorem sgn_eq_one (k : Kˣ) : sgn (J := J) σ k = 1 := by
  have := H.finite
  have h2 := H.two_ne
  by_contra hne
  have hk0 : sgn (J := J) σ k = -1 := (H.sgn_eq k).resolve_left hne
  have hns : ∀ m : Kˣ, ¬IsSquare (m : K) → sgn (J := J) σ m = -1 := by
    intro m hm
    have hk : ¬IsSquare (k : K) := by
      intro hsq
      rw [H.sgn_of_isSquare hsq] at hk0
      exact h2 (by linear_combination hk0)
    have hmk : IsSquare ((m * k : Kˣ) : K) := by
      rw [Units.val_mul]; exact H.isSquare_mul_of_not m.ne_zero k.ne_zero hm hk
    have e := H.sgn_mul m k
    rw [H.sgn_of_isSquare hmk, hk0] at e
    linear_combination e
  obtain ⟨κ, hκ0, hκc, hκF⟩ := H.exists_F_center
  obtain ⟨l, hl0, hlc, hll⟩ := H.exists_sqrt_kappa hκ0 hκc hκF
  obtain ⟨w, hw, hFw⟩ := H.fix_exists'
  obtain ⟨c, hc0, hcc⟩ := H.exists_trace_zero
  set z : Coord J := zc c hcc with hzdef
  have hz : z ≠ 1 := fun e => hc0 (congrArg (fun v : Coord J => v.1.2) e)
  have hz0 : z.1.1 = 0 := rfl
  have hz2 : z.1.2 = c := rfl
  have hzz := H.zm_twice hκc hκF hw hFw hz hz0
  have hy : c ^ 2 / κ ≠ 0 := div_ne_zero (pow_ne_zero _ hc0) hκ0
  have hyc : J.conj (c ^ 2 / κ) = c ^ 2 / κ := by rw [map_div₀, map_pow, hcc, neg_sq, hκc]
  obtain ⟨k₁, hk₁⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hy hyc
  have hk₁' : (k₁ : K) * J.conj (k₁ : K) = c ^ 2 / κ := hk₁
  have hFz : F z = hermitianTorusAction J k₁ z := by
    apply coord_ext
    · rw [(hκF z hz hz0).1, torus_fst, hz0]; ring
    · rw [F_zc hκF hz hz0, torus_snd, hz2, mul_assoc, ← mul_inv, mul_comm (J.conj _), hk₁']
      field_simp
  have hht := H.h_center_torus k₁ hz
  rw [← hFz] at hht
  have hk₁ns : ¬IsSquare (k₁ : K) := by
    apply not_isSquare_of_nrm
    intro r hr e
    rw [hk₁', ← hll] at e
    have : (r * l - c) * (r * l + c) = 0 := by
      field_simp at e; linear_combination e
    have hc' : J.conj c = c := by
      rcases mul_eq_zero.mp this with h | h
      · have : c = r * l := by linear_combination -h
        rw [this, map_mul, hr, hlc]
      · have : c = -(r * l) := by linear_combination h
        rw [this, map_neg, map_mul, hr, hlc]
    rw [hcc] at hc'
    exact hc0 (by
      have : 2 * c = 0 := by linear_combination -hc'
      exact (mul_eq_zero.mp this).resolve_left h2)
  rw [hns k₁ hk₁ns, hk₁'] at hht
  have hhz := (h z).ne_zero
  have hFhz := (h (F z)).ne_zero
  have hcube : ((h (F z) : K)) ^ 3 = (-1 * (h z : K) / (c ^ 2 / κ)) ^ 3 := by
    have hden : (-1 * (h z : K) / (c ^ 2 / κ)) ≠ 0 :=
      div_ne_zero (mul_ne_zero (neg_ne_zero.mpr one_ne_zero) hhz) hy
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hden)] at hht
    exact hht
  set θ := (h z : K) * l / c with hθdef
  have hθ6 : θ ^ 6 = -1 := by
    rw [mul_pow, hcube] at hzz
    rw [hθdef]
    field_simp at hzz ⊢
    rw [← hll] at hzz
    linear_combination -hzz
  have hNθ : θ * J.conj θ = 1 := by
    have hn := H.nrm_h_center hκc hκF hz hz0
    rw [hz2, ← hll] at hn
    rw [hθdef, map_div₀, map_mul, hlc, hcc]
    field_simp
    linear_combination -hn
  set ψ := θ ^ 3 with hψdef
  have hψ2 : ψ * ψ = -1 := by rw [hψdef, ← pow_add]; exact hθ6
  have hNψ : ψ * J.conj ψ = 1 := by
    rw [hψdef, map_pow, ← mul_pow, hNθ, one_pow]
  have hψc : J.conj ψ = -ψ := by
    have e : J.conj ψ * J.conj ψ = ψ * ψ := by rw [← map_mul, hψ2, map_neg, map_one]
    have : (J.conj ψ - ψ) * (J.conj ψ + ψ) = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h | h
    · exfalso
      have hc : J.conj ψ = ψ := by linear_combination h
      exact h2 (by linear_combination -hNψ + hψ2 + ψ * hc)
    · linear_combination h
  obtain ⟨k₂, hk₂⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega)
    (neg_ne_zero.mpr one_ne_zero) (by rw [map_neg, map_one])
  have hk₂' : (k₂ : K) * J.conj (k₂ : K) = -1 := hk₂
  have hk₂ns : ¬IsSquare (k₂ : K) := by
    apply not_isSquare_of_nrm
    intro r hr e
    rw [hk₂', ← hψ2] at e
    have : (r - ψ) * (r + ψ) = 0 := by linear_combination e
    have hc' : J.conj ψ = ψ := by
      rcases mul_eq_zero.mp this with h | h
      · have : ψ = r := by linear_combination -h
        rw [← this] at hr; exact hr
      · have : ψ = -r := by linear_combination h
        rw [this, map_neg, hr]
    rw [hψc] at hc'
    have : ψ = 0 := by
      have : 2 * ψ = 0 := by linear_combination -hc'
      exact (mul_eq_zero.mp this).resolve_left h2
    rw [this, mul_zero] at hψ2
    exact one_ne_zero (by linear_combination hψ2)
  have hs₂ := hns k₂ hk₂ns
  have hfix : ∀ X : Coord J, hermitianTorusAction J (σ k₂) X = hermitianTorusAction J k₂ X := by
    intro X
    rw [H.t_sigma k₂ X]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, cj_val, hs₂]
    have hck : J.conj (k₂ : K) ≠ 0 := (map_ne_zero J.conj).2 k₂.ne_zero
    field_simp
    linear_combination -hk₂'
  have := H.σ_fix k₂ hfix
  rw [hk₂'] at this
  exact h2 (by linear_combination -this)

theorem t_sigma' (k : Kˣ) (X : Coord J) :
    hermitianTorusAction J (σ k) X = hermitianTorusAction J (cj J k)⁻¹ X := by
  rw [H.t_sigma k X]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mk0, H.sgn_eq_one, one_mul]

theorem h_center_torus' (k : Kˣ) {z : Coord J} (hz : z ≠ 1) :
    (h (hermitianTorusAction J k z) : K) ^ 3 =
      ((h z : K) / ((k : K) * J.conj (k : K))) ^ 3 := by
  have hk := k.ne_zero
  have hck : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  have e := H.h_center_torus k hz
  rw [H.sgn_eq_one, one_mul, div_pow, div_eq_one_iff_eq] at e
  · exact e
  · exact pow_ne_zero _ (div_ne_zero (h z).ne_zero (mul_ne_zero hk hck))

theorem exists_mu {κ : K} (hκ0 : κ ≠ 0) (hκc : J.conj κ = κ)
    (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 → (F z).1.1 = 0 ∧ (F z).1.2 * z.1.2 = κ) :
    ∃ μ : K, μ ≠ 0 ∧ J.conj μ = μ ∧ μ * μ = κ ∧
      ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 → ((h z : K) * μ / z.1.2) ^ 3 = 1 := by
  have := H.finite
  have h2 := H.two_ne
  obtain ⟨l, hl0, hlc, hll⟩ := H.exists_sqrt_kappa hκ0 hκc hκF
  obtain ⟨w, hw, hFw⟩ := H.fix_exists'
  obtain ⟨c₁, hc₁, hcc₁⟩ := H.exists_trace_zero
  set z₁ : Coord J := zc c₁ hcc₁ with hz₁def
  have hz₁ : z₁ ≠ 1 := fun e => hc₁ (congrArg (fun v : Coord J => v.1.2) e)
  have hz₁0 : z₁.1.1 = 0 := rfl
  have hz₁2 : z₁.1.2 = c₁ := rfl
  have hzz := H.zm_twice hκc hκF hw hFw hz₁ hz₁0
  have hy : c₁ ^ 2 / κ ≠ 0 := div_ne_zero (pow_ne_zero _ hc₁) hκ0
  have hyc : J.conj (c₁ ^ 2 / κ) = c₁ ^ 2 / κ := by rw [map_div₀, map_pow, hcc₁, neg_sq, hκc]
  obtain ⟨k₁, hk₁⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hy hyc
  have hk₁' : (k₁ : K) * J.conj (k₁ : K) = c₁ ^ 2 / κ := hk₁
  have hFz : F z₁ = hermitianTorusAction J k₁ z₁ := by
    apply coord_ext
    · rw [(hκF z₁ hz₁ hz₁0).1, torus_fst, hz₁0]; ring
    · rw [F_zc hκF hz₁ hz₁0, torus_snd, hz₁2, mul_assoc, ← mul_inv, mul_comm (J.conj _), hk₁']
      field_simp
  have hht := H.h_center_torus' k₁ hz₁
  rw [← hFz, hk₁'] at hht
  have hhz := (h z₁).ne_zero
  have hzz' : (h z₁ : K) ^ 6 * κ ^ 3 = c₁ ^ 6 := by
    rw [mul_pow, hht] at hzz
    field_simp at hzz
    linear_combination hzz
  have hθ6 : (((h z₁ : K) * l / c₁) ^ 3) ^ 2 = 1 := by
    rw [← pow_mul, div_pow, mul_pow, show 3 * 2 = 6 from rfl,
      show l ^ 6 = κ ^ 3 by rw [← hll]; ring]
    field_simp
    linear_combination hzz'
  have hs : ((h z₁ : K) * l / c₁) ^ 3 = 1 ∨ ((h z₁ : K) * l / c₁) ^ 3 = -1 := by
    have : (((h z₁ : K) * l / c₁) ^ 3 - 1) * (((h z₁ : K) * l / c₁) ^ 3 + 1) = 0 := by
      linear_combination hθ6
    rcases mul_eq_zero.mp this with e | e
    · left; linear_combination e
    · right; linear_combination e
  obtain ⟨s₁, hs₁def, hs₁⟩ : ∃ s₁ : K, ((h z₁ : K) * l / c₁) ^ 3 = s₁ ∧ (s₁ = 1 ∨ s₁ = -1) :=
    ⟨_, rfl, hs⟩
  have hs₁sq : s₁ ^ 2 = 1 := by rcases hs₁ with e | e <;> rw [e] <;> ring
  have hs₁c : J.conj s₁ = s₁ := by rcases hs₁ with e | e <;> rw [e] <;> simp
  have hs₁0 : s₁ ≠ 0 := by rcases hs₁ with e | e <;> rw [e] <;> norm_num
  have hθ3' : (h z₁ : K) ^ 3 * l ^ 3 = s₁ * c₁ ^ 3 := by
    rw [div_pow, mul_pow] at hs₁def
    field_simp at hs₁def
    linear_combination hs₁def
  refine ⟨s₁ * l, mul_ne_zero hs₁0 hl0, by rw [map_mul, hs₁c, hlc], ?_, ?_⟩
  · rw [← hll]; linear_combination (l * l) * hs₁sq
  · intro z hz hz0
    have hc := coord_snd_ne_zero J hz
    have hcc : J.conj z.1.2 = -z.1.2 := conj_snd_of_fst_eq_zero hz0
    have hx : c₁ / z.1.2 ≠ 0 := div_ne_zero hc₁ hc
    have hxc : J.conj (c₁ / z.1.2) = c₁ / z.1.2 := by rw [map_div₀, hcc₁, hcc, neg_div_neg_eq]
    obtain ⟨k, hk⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hx hxc
    have hk' : (k : K) * J.conj (k : K) = c₁ / z.1.2 := hk
    have hkz : hermitianTorusAction J k z₁ = z := by
      apply coord_ext
      · rw [torus_fst, hz₁0, hz0]; ring
      · rw [torus_snd, hz₁2, mul_assoc, ← mul_inv, mul_comm (J.conj _), hk']
        field_simp
    have e := H.h_center_torus' k hz₁
    rw [hkz, hk'] at e
    rw [div_pow, mul_pow, e]
    field_simp
    linear_combination s₁ ^ 3 * hθ3' + (s₁ ^ 2 + 1) * c₁ ^ 3 * hs₁sq

end SMapHyp3

end CFSG.UnitaryThreeRecognition.DThree
