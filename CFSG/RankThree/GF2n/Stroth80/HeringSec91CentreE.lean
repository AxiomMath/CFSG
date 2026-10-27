module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.HardMathSupport.Seitz.Proving.SL2PrimeOrder
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.GF2n.Stroth80
namespace HS9

open CFSG.ClassicalGroups.Orthogonal QuadraticMap Polynomial

theorem mul_sub_one_mul_eq_zero91 {R : Type*} [Ring R] (h2 : (2 : R) = 0) {x y s : R}
    (hx : x * x = 1) (hy : y * y = 1) (hs : ∀ z, s * z = z * s)
    (hm : (x + y) * (x + y) * (x + y) = s * (x + y)) :
    (x * y - 1) * ((x * y) ^ 2 - s * (x * y) + 1) = 0 := by
  have hneg : ∀ z : R, -z = z := fun z =>
    neg_eq_of_add_eq_zero_right (by rw [← two_mul, h2, zero_mul])
  have e1 : x * y + 1 = x * (x + y) := by rw [mul_add, hx, add_comm]
  have e2 : x * y * (x * y) + 1 = (x + y) * (x + y) * (x * y) := by
    have : (x + y) * (x + y) * (x * y) =
        (x * x) * (x * y) + x * y * (x * y) + y * (x * x) * y + (y * y) * (x * y) := by
      noncomm_ring
    have h2xy : x * y + x * y = 0 := by rw [← two_mul, h2, zero_mul]
    simp only [this, hx, hy, one_mul, mul_one]
    rw [show x * y + x * y * (x * y) + 1 + x * y = x * y * (x * y) + 1 + (x * y + x * y) by abel,
      h2xy, add_zero]
  simp only [sub_eq_add_neg, hneg, _root_.sq]
  calc (x * y + 1) * (x * y * (x * y) + s * (x * y) + 1)
      = x * (x + y) * ((x + y) * (x + y) * (x * y) + s * (x * y)) := by
        rw [e1, add_right_comm, e2]
    _ = x * ((x + y) * (x + y) * (x + y) + s * (x + y)) * (x * y) := by
        rw [hs (x + y)]
        noncomm_ring
    _ = 0 := by rw [hm, ← two_mul, h2, zero_mul, mul_zero, zero_mul]

theorem exists_trace_dvd91 {K : Type*} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hr : r.Prime)
    (hrq : r ∣ Nat.card K ^ 2 - 1) :
    ∃ t : K, t ≠ 0 ∧ (X - 1) * (X ^ 2 - C t * X + 1) ∣ (X ^ r - 1 : K[X]) := by
  obtain ⟨h, hh⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hr hrq
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h2q : 2 ∣ Nat.card K := by
      letI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).1 (Nat.cast_card_eq_zero K)
    have hq1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    obtain ⟨m, hm⟩ := h2q
    have : Nat.card K ^ 2 = 4 * (m * m) := by rw [hm]; ring
    omega
  set M : Matrix (Fin 2) (Fin 2) K := (h : Matrix (Fin 2) (Fin 2) K) with hMdef
  have hdet : M.det = 1 := h.2
  have hMr : M ^ r = 1 := by
    rw [hMdef, ← Matrix.SpecialLinearGroup.coe_pow, ← hh, pow_orderOf_eq_one,
      Matrix.SpecialLinearGroup.coe_one]
  have hh1 : h ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hh
    exact hr.one_lt.ne hh
  have hns : M ∉ (algebraMap K (Matrix (Fin 2) (Fin 2) K)).range := by
    rintro ⟨l, hl⟩
    have hl2 : l ^ 2 = 1 := by
      rw [← hdet, ← hl, Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Fintype.card_fin,
        Matrix.det_one, mul_one]
    have h0 : (l + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, hl2, one_pow, CharTwo.add_self_eq_zero]
    have hl1 : l = 1 :=
      (eq_neg_of_add_eq_zero_left (pow_eq_zero_iff two_ne_zero |>.1 h0)).trans
        (CharTwo.neg_eq 1)
    apply hh1
    apply Subtype.ext
    show M = 1
    rw [← hl, hl1, map_one]
  have hint : IsIntegral K M := IsIntegral.of_finite K M
  have hmin : M.charpoly = minpoly K M := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Matrix.charpoly_monic M) (Matrix.minpoly_dvd_charpoly M) ?_
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    exact (minpoly.two_le_natDegree_iff hint).2 hns
  have hP : M.charpoly ∣ X ^ r - 1 := by
    rw [hmin]
    apply minpoly.dvd
    simp [hMr]
  rw [Matrix.charpoly_fin_two, hdet, map_one] at hP
  have ht0 : M.trace ≠ 0 := by
    intro h0
    have hCH := Matrix.aeval_self_charpoly M
    rw [Matrix.charpoly_fin_two, h0, hdet] at hCH
    simp only [map_zero, zero_mul, sub_zero, map_add, map_pow, aeval_X, map_one] at hCH
    have hM2 : M ^ 2 = 1 := (eq_neg_of_add_eq_zero_left hCH).trans (CharTwo.neg_eq 1)
    have hh2 : h ^ 2 = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; exact hM2)
    have hdvd := orderOf_dvd_of_pow_eq_one hh2
    rw [hh] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hdvd)
  refine ⟨M.trace, ht0, ?_⟩
  have hcop : IsCoprime (X - 1 : K[X]) (X ^ 2 - C M.trace * X + 1) := by
    rw [← C_1]
    refine (Polynomial.irreducible_X_sub_C 1).coprime_iff_not_dvd.2 ?_
    rw [Polynomial.dvd_iff_isRoot]
    intro hroot
    have h1 : eval 1 (X ^ 2 - C M.trace * X + C 1) = 0 := hroot
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at h1
    apply ht0
    linear_combination -h1 + h2
  exact hcop.mul_dvd (by simpa using sub_dvd_pow_sub_pow (X : K[X]) 1 r) hP

theorem exists_eichler_pair_order91 {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {u u' a : V} (hu : Q u = 0) (hu' : Q u' = 0)
    (hp : polar Q u u' ≠ 0) (ha : polar Q u a = 0) (ha' : polar Q u' a = 0) (hc : Q a ≠ 0)
    {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K ^ 2 - 1) :
    ∃ κ : K, κ ≠ 0 ∧ (eichler Q u' (κ • a) * eichler Q u a) ^ r = 1 := by
  obtain ⟨t, ht0, S, hS⟩ := exists_trace_dvd91 hr hrq
  obtain ⟨τ, hτ⟩ := isSquare_of_charTwo' t
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hτ
    exact ht0 hτ
  generalize hpdef : polar Q u u' = p at hp
  generalize hcdef : Q a = c at hc
  set κ : K := τ * (c * p)⁻¹ with hκdef
  have hκ0 : κ ≠ 0 := mul_ne_zero hτ0 (inv_ne_zero (mul_ne_zero hc hp))
  have hκcp : κ * c * p = τ := by
    rw [hκdef]
    field_simp
  refine ⟨κ, hκ0, ?_⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h2V : ∀ w : V, w + w = 0 := fun w => by rw [← two_smul K w, h2, zero_smul]
  have hκa : polar Q u' (κ • a) = 0 := by rw [polar_smul_right_eq, ha', mul_zero]
  have hBuu : polar Q u u = 0 := polar_self_eq_zero hu
  have hBu'u' : polar Q u' u' = 0 := polar_self_eq_zero hu'
  have hBaa : polar Q a a = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hBau : polar Q a u = 0 := by rw [polar_comm, ha]
  have hBau' : polar Q a u' = 0 := by rw [polar_comm, ha']
  have hBu'u : polar Q u' u = p := by rw [polar_comm, hpdef]
  set x := eichler Q u' (κ • a) with hxdef
  set y := eichler Q u a with hydef
  set X₀ : Module.End K V := x.toLinearMap
  set Y₀ : Module.End K V := y.toLinearMap
  set m : Module.End K V := X₀ + Y₀
  have hm : ∀ z, m z = (κ * polar Q z u' + polar Q z u) • a +
      (κ * polar Q z a + κ ^ 2 * c * polar Q z u') • u' + (polar Q z a + c * polar Q z u) • u := by
    intro z
    show x z + y z = _
    rw [hxdef, hydef, eichler_apply hu' hκa, eichler_apply hu ha, polar_smul_right_eq,
      map_smul_eq_sq, hcdef]
    linear_combination (norm := module) h2V z -
      (κ * polar Q z a + κ ^ 2 * c * polar Q z u') • h2V u' -
      (polar Q z a + c * polar Q z u) • h2V u
  have hmu : ∀ z, polar Q (m z) u = (κ * polar Q z a + κ ^ 2 * c * polar Q z u') * p := by
    intro z
    rw [hm, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
      polar_smul_left_eq, hBau, hBu'u, hBuu]
    ring
  have hmu' : ∀ z, polar Q (m z) u' = (polar Q z a + c * polar Q z u) * p := by
    intro z
    rw [hm, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
      polar_smul_left_eq, hBau', hBu'u', hpdef]
    ring
  have hma : ∀ z, polar Q (m z) a = 0 := by
    intro z
    rw [hm, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
      polar_smul_left_eq, hBaa, ha', ha]
    ring
  have hcube : m * m * m = algebraMap K (Module.End K V) t * m := by
    refine LinearMap.ext fun z => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply]
    rw [hm (m (m z)), hmu (m z), hmu' (m z), hma (m z), hma z, hmu z, hmu' z, hm z, hτ, ← hκcp]
    linear_combination (norm := module) (κ ^ 2 * c * polar Q z a * p ^ 2) • h2V a
  have hxx : X₀ * X₀ = 1 := by
    refine LinearMap.ext fun z => ?_
    show x (x z) = z
    rw [← LinearEquiv.mul_apply, hxdef, eichler_mul hκa hκa, h2V, eichler_zero_right]
    rfl
  have hyy : Y₀ * Y₀ = 1 := by
    refine LinearMap.ext fun z => ?_
    show y (y z) = z
    rw [← LinearEquiv.mul_apply, hydef, eichler_mul ha ha, h2V, eichler_zero_right]
    rfl
  have h2E : (2 : Module.End K V) = 0 := by
    refine LinearMap.ext fun z => ?_
    rw [← one_add_one_eq_two, LinearMap.add_apply, Module.End.one_apply, h2V,
      LinearMap.zero_apply]
  have hring := mul_sub_one_mul_eq_zero91 h2E hxx hyy (fun z => Algebra.commutes t z) hcube
  have hG : (X₀ * Y₀) ^ r = 1 := by
    have := congrArg (Polynomial.aeval (X₀ * Y₀)) hS
    simp only [map_sub, map_pow, aeval_X, map_one, map_mul, map_add, aeval_C] at this
    rw [hring, zero_mul] at this
    exact sub_eq_zero.1 this
  have hfun : ⇑(x * y) = ⇑(X₀ * Y₀) := rfl
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.coe_pow, hfun, ← Module.End.coe_pow, hG]
  rfl

end HS9
end CFSG.RankThree.GF2n.Stroth80
