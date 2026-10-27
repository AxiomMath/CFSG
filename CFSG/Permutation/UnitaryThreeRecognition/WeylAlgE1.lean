module

public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgMoufang
public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgBlock

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

theorem zc_congr {c c' : K} (hc : J.conj c = -c) (hc' : J.conj c' = -c') (e : c = c') :
    zc c hc = zc c' hc' := by subst e; rfl

@[expose] noncomputable def theta (h : Coord J → Kˣ) (c : K) (hc : J.conj c = -c) : K :=
  (h (zc c hc) : K) * (J.conj (h (zc c hc) : K))⁻¹ ^ 2

variable [Finite K] {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ →* Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp

variable (H : SMapHyp J q F σ h)
include H

omit [Finite K] in
theorem h_zc_torus (k : Kˣ) {c : K} (hc0 : c ≠ 0) (hc : J.conj c = -c) :
    (h (zc (c * (J.conj (k : K))⁻¹ * (k : K)⁻¹) (conj_div_nrm hc k)) : K) =
      eps J σ k * (h (zc c hc) : K) / nrm J k := by
  have hz1 : zc c hc ≠ 1 := fun e => hc0 (congrArg (fun v : Coord J => v.1.2) e)
  have h1 := H.h_torus k (zc c hc) hz1 rfl
  rw [torus_zc] at h1
  rw [h1, Units.val_mul, Units.val_mul, sigma_val, nrm_def]
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hck0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  rw [Units.val_inv_eq_inv_val]
  field_simp

theorem theta_eq {c₁ : K} (hc₁0 : c₁ ≠ 0) (hc₁ : J.conj c₁ = -c₁) {c : K} (hc0 : c ≠ 0)
    (hc : J.conj c = -c) :
    theta h c hc = sgn J σ (c₁ / c) * (c₁ * theta h c₁ hc₁) / c := by
  have hx : c₁ / c ≠ 0 := div_ne_zero hc₁0 hc0
  have hxc : J.conj (c₁ / c) = c₁ / c := by rw [map_div₀, hc₁, hc, neg_div_neg_eq]
  obtain ⟨k, hk⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hx hxc
  have hk' : (k : K) * J.conj (k : K) = c₁ / c := hk
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hck0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  have harg : c₁ * (J.conj (k : K))⁻¹ * (k : K)⁻¹ = c := by
    rw [mul_assoc, ← mul_inv, mul_comm (J.conj _), hk']; field_simp
  have hzc : zc c hc = zc (c₁ * (J.conj (k : K))⁻¹ * (k : K)⁻¹) (conj_div_nrm hc₁ k) :=
    zc_congr _ _ harg.symm
  have hh := H.h_zc_torus k hc₁0 hc₁
  rw [← hzc, hk] at hh
  have hsg : sgn J σ (c₁ / c) = eps J σ k := by rw [← hk]; exact H.sgn_nrm k
  have he := H.eps_mul_self k
  have he0 : eps J σ k ≠ 0 := by intro e; rw [e, zero_mul] at he; exact zero_ne_one he
  have hh1 : (h (zc c₁ hc₁) : K) ≠ 0 := (h _).ne_zero
  have hch1 : J.conj (h (zc c₁ hc₁) : K) ≠ 0 := (map_ne_zero J.conj).2 hh1
  rw [theta, theta, hh, hsg, map_div₀, map_mul, H.conj_eps, hxc]
  field_simp
  linear_combination (-1 : K) * he

omit H [Finite K] in
theorem tr_ne_zero_of_fst {w : Coord J} (hw : w.1.1 ≠ 0) : w.1.2 + J.conj w.1.2 ≠ 0 := by
  have := coord_rel w
  intro e
  rw [e, zero_add] at this
  exact (mul_ne_zero hw ((map_ne_zero J.conj).2 hw)) this

theorem E1 {κ : K} (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 →
      (F z).1.1 = 0 ∧ (F z).1.2 = κ / z.1.2)
    (hκc : J.conj κ = κ) {c₀ : K} (hc₀0 : c₀ ≠ 0)
    (hgam : ∀ b : K, b + J.conj b ≠ 0 → gam J F b = c₀ * sgn J σ (nn J b) / J.conj b)
    {c₁ : K} (hc₁0 : c₁ ≠ 0) (hc₁ : J.conj c₁ = -c₁)
    {w : Coord J} (hw : w.1.1 ≠ 0) {c : K} (hc0 : c ≠ 0) (hc : J.conj c = -c) :
    (c * J.conj (emm J F w.1.2) - κ) * J.conj w.1.2 =
      c₀ * (c₁ * theta h c₁ hc₁) * (sgn J σ (nn J (w.1.2 + c)) *
        sgn J σ (nn J (κ / c + emm J F w.1.2)) * sgn J σ (nn J w.1.2) *
        sgn J σ (c₁ / c)) * (J.conj w.1.2 - c) := by
  have hmou := H.moufang_fst hκF hκc hc0 hc hw
  change gam J F (w.1.2 + c) = theta h c hc * gam J F (κ / c + emm J F w.1.2) *
    gam J F w.1.2 at hmou
  have hb : w.1.2 + J.conj w.1.2 ≠ 0 := tr_ne_zero_of_fst hw
  have hFw := H.F_ne_center hw
  have hM : emm J F w.1.2 + J.conj (emm J F w.1.2) ≠ 0 := by
    have := tr_ne_zero_of_fst hFw
    rwa [H.F_snd_eq hw] at this
  have hb1 : (w.1.2 + c) + J.conj (w.1.2 + c) ≠ 0 := by
    rw [map_add, hc]; convert hb using 1; ring
  have hb2 : (κ / c + emm J F w.1.2) + J.conj (κ / c + emm J F w.1.2) ≠ 0 := by
    rw [map_add, map_div₀, hκc, hc]; convert hM using 1; field_simp; ring
  rw [hgam _ hb1, hgam _ hb2, hgam _ hb, H.theta_eq hc₁0 hc₁ hc0 hc] at hmou
  have hb0 : w.1.2 ≠ 0 := by intro e; apply hb; rw [e, map_zero, add_zero]
  have hcb0 : J.conj w.1.2 ≠ 0 := (map_ne_zero J.conj).2 hb0
  have hD1 : J.conj w.1.2 - c ≠ 0 := by
    intro e
    apply hb
    have e' : J.conj w.1.2 = c := sub_eq_zero.mp e
    have : w.1.2 = -c := by have := congrArg J.conj e'; rwa [conj_conj, hc] at this
    rw [this, map_neg, hc]; ring
  have hc2 : J.conj (κ / c + emm J F w.1.2) = -(κ / c) + J.conj (emm J F w.1.2) := by
    rw [map_add, map_div₀, hκc, hc, div_neg]
  have hD2 : -(κ / c) + J.conj (emm J F w.1.2) ≠ 0 := by
    intro e
    apply hb2
    have e' : J.conj (κ / c + emm J F w.1.2) = 0 := by rw [hc2]; exact e
    have : κ / c + emm J F w.1.2 = 0 := by
      have := congrArg J.conj e'; rwa [conj_conj, map_zero] at this
    rw [e', this, add_zero]
  have hc1 : J.conj (w.1.2 + c) = J.conj w.1.2 - c := by rw [map_add, hc]; ring
  rw [hc1, hc2] at hmou
  have hs1 := H.sgn_mul_self (nn J (w.1.2 + c))
  have hD2' : c * J.conj (emm J F w.1.2) - κ ≠ 0 := by
    intro e
    apply hD2
    rw [show -(κ / c) + J.conj (emm J F w.1.2) = (c * J.conj (emm J F w.1.2) - κ) / c by
      field_simp; ring, e, zero_div]
  generalize sgn J σ (nn J (w.1.2 + c)) = s₁ at hmou hs1 ⊢
  generalize sgn J σ (nn J (κ / c + emm J F w.1.2)) = s₂ at hmou ⊢
  generalize sgn J σ (nn J w.1.2) = s₃ at hmou ⊢
  generalize sgn J σ (c₁ / c) = s₄ at hmou ⊢
  generalize c₁ * theta h c₁ hc₁ = R at hmou ⊢
  generalize J.conj (emm J F w.1.2) = M' at hmou hD2 hD2' ⊢
  generalize J.conj w.1.2 = B at hmou hcb0 hD1 ⊢
  have e2 : -(κ / c) + M' = (c * M' - κ) / c := by field_simp; ring
  rw [e2] at hmou
  have e1 : s₁ * ((c * M' - κ) * B) = c₀ * R * s₂ * s₃ * s₄ * (B - c) := by
    field_simp at hmou
    linear_combination hmou
  linear_combination s₁ * e1 - ((c * M' - κ) * B) * hs1

end SMapHyp

end CFSG.UnitaryThreeRecognition.WeylAlg
