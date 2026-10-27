module

public import CFSG.LieType.Universal.Spin.Twisted.RankOne
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Timmesfeld.ARS.CaseOADeg

open CFSG.LieType.Universal.Spin.Twisted

section Dict

variable {F K : Type} [Field F] [Field K] (σ : K ≃+* K) (ι : F →+* K) (ζ : K)

@[expose] def kap (p : Fin 2 → F) : K := ι (p 0) + ι (p 1) * ζ

theorem kap_add (p q : Fin 2 → F) : kap ι ζ (p + q) = kap ι ζ p + kap ι ζ q := by
  simp only [kap, Pi.add_apply, map_add]
  ring

theorem kap_smul (s : F) (p : Fin 2 → F) : kap ι ζ (s • p) = kap ι ζ p * ι s := by
  simp only [kap, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem kap_planeOne : kap ι ζ (planeOne : Fin 2 → F) = 1 := by
  simp [kap, planeOne]

variable {σ ι ζ} {b c : F} (hb : ι b = ζ + σ ζ) (hc : ι c = ζ * σ ζ) (hι : ∀ x, σ (ι x) = ι x)

include hb hc hι

theorem norm_kap (p : Fin 2 → F) : σ (kap ι ζ p) * kap ι ζ p = ι (planeNorm b c p) := by
  simp only [kap, planeNorm, map_add, map_mul, map_pow, hι, hb, hc]
  ring

theorem polar_kap (p q : Fin 2 → F) :
    kap ι ζ p * σ (kap ι ζ q) + σ (kap ι ζ p) * kap ι ζ q = ι (polarPlane b c p q) := by
  simp only [kap, polarPlane, map_add, map_mul, map_ofNat, hι, hb, hc]
  ring

omit hc in
theorem kap_planeRefl [CharP K 2] (p : Fin 2 → F) :
    kap ι ζ (planeRefl b c planeOne p) = σ (kap ι ζ p) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [planeRefl, planeNorm_planeOne, div_one]
  simp only [polarPlane, planeOne, kap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, zero_add, add_zero, one_mul,
    sub_zero, map_sub, map_add, map_mul, map_ofNat, hι, hb]
  linear_combination (-(ι (p 0) + ι (p 1) * σ ζ)) * h2

omit hι in
@[expose] noncomputable def lam : ShortField b c →+* K where
  toFun t := ι t.re + ι t.im * ζ
  map_one' := by
    change ι 1 + ι 0 * ζ = 1
    simp
  map_mul' s t := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_neg, hb, hc]
    ring
  map_zero' := by simp
  map_add' s t := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]
    ring

omit hι in
theorem lam_apply (t : ShortField b c) : lam hb hc t = ι t.re + ι t.im * ζ := rfl

omit hι in
theorem kap_fieldCoord (t : ShortField b c) : kap ι ζ (fieldCoord t) = lam hb hc t := by
  simp [kap, fieldCoord, lam_apply]

theorem kap_starCoord [CharP K 2] (t : ShortField b c) :
    kap ι ζ (starCoord t) = σ (lam hb hc t) := by
  have hn : ∀ x : K, -x = x := CharTwo.neg_eq
  simp only [kap, starCoord, lam_apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_neg,
    map_add, map_mul, hι, hb, hn]
  have h2 : ι t.im * ζ + ι t.im * ζ = 0 := CharTwo.add_self_eq_zero _
  linear_combination h2

omit hb hc hι in
theorem kap_surjective (hσ : ∀ x, σ (σ x) = x) (hζ : σ ζ ≠ ζ)
    (hsurj : ∀ x : K, σ x = x → ∃ y : F, ι y = x) (t : K) : ∃ p : Fin 2 → F, kap ι ζ p = t := by
  have hd : ζ - σ ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hζ)
  set y := (t - σ t) / (ζ - σ ζ) with hy
  have hyσ : σ y = y := by
    rw [hy, map_div₀, map_sub, map_sub, hσ, hσ]
    rw [show σ t - t = -(t - σ t) by ring, show σ ζ - ζ = -(ζ - σ ζ) by ring, neg_div_neg_eq]
  set x := t - y * ζ with hx
  have hxσ : σ x = x := by
    rw [hx, map_sub, map_mul, hyσ]
    have e : y * (ζ - σ ζ) = t - σ t := by rw [hy, div_mul_cancel₀ _ hd]
    linear_combination e
  obtain ⟨x', hx'⟩ := hsurj x hxσ
  obtain ⟨y', hy'⟩ := hsurj y hyσ
  refine ⟨![x', y'], ?_⟩
  simp only [kap, Matrix.cons_val_zero, Matrix.cons_val_one, hx', hy', hx]
  ring

end Dict

end CFSG.Timmesfeld.ARS.CaseOADeg
