module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

public section

namespace CFSG.RankThree.PartOne.KFU

open Module

section Heis

variable {K : Type} [Field K]

theorem heis_const {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (l m : Fin 5 → K) (hl : ∀ i, l i ≠ 0)
    (f : Matrix (Fin 5) (Fin 5) K) (hf : f.det ≠ 0)
    (hfa : ∀ i j, f i j * l j = ζ * l i * f i j) (hfb : ∀ i j, f i j * m j = m i * f i j) :
    ∀ i j, m i = m j := by
  classical
  have hrow : ∀ i, ∃ j, f i j ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    exact hf (Matrix.det_eq_zero_of_row_eq_zero i h)
  choose σ hσ using hrow
  have hl' : ∀ i, l (σ i) = ζ * l i := fun i => by
    have h1 := hfa i (σ i)
    have h2 : f i (σ i) * l (σ i) = f i (σ i) * (ζ * l i) := by rw [h1]; ring
    exact mul_left_cancel₀ (hσ i) h2
  have hm' : ∀ i, m (σ i) = m i := fun i => by
    have h1 := hfb i (σ i)
    have h2 : f i (σ i) * m (σ i) = f i (σ i) * m i := by rw [h1]; ring
    exact mul_left_cancel₀ (hσ i) h2
  have hlt : ∀ (t : ℕ) (i : Fin 5), l (σ^[t] i) = ζ ^ t * l i := by
    intro t i
    induction t with
    | zero => simp
    | succ t ih => rw [Function.iterate_succ_apply', hl', ih, pow_succ]; ring
  have hmt : ∀ (t : ℕ) (i : Fin 5), m (σ^[t] i) = m i := by
    intro t i
    induction t with
    | zero => simp
    | succ t ih => rw [Function.iterate_succ_apply', hm', ih]
  intro i j
  have hinj : Function.Injective (fun t : Fin 5 => σ^[t.val] i) := by
    intro s t hst
    have h1 : ζ ^ s.val * l i = ζ ^ t.val * l i := by
      rw [← hlt, ← hlt]
      exact congrArg l hst
    have h2 : ζ ^ s.val = ζ ^ t.val := mul_right_cancel₀ (hl i) h1
    exact Fin.ext (hζ.pow_inj s.2 t.2 h2)
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.mp hinj) j
  rw [← ht]
  exact (hmt t.val i).symm

end Heis

section Comm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem comm_scalar_pow_finrank (W : Submodule K V) (x y : V →ₗ[K] V)
    (hx : ∀ w ∈ W, x w ∈ W) (hy : ∀ w ∈ W, y w ∈ W)
    (hxi : Function.Injective x) (hyi : Function.Injective y) (c : K)
    (hxy : ∀ v, x (y v) = c • y (x v)) : c ^ finrank K W = 1 := by
  classical
  let x' : W →ₗ[K] W := x.restrict hx
  let y' : W →ₗ[K] W := y.restrict hy
  have hx'i : Function.Injective x' := fun a b h => Subtype.ext (hxi (congrArg Subtype.val h))
  have hy'i : Function.Injective y' := fun a b h => Subtype.ext (hyi (congrArg Subtype.val h))
  have hxu : IsUnit (LinearMap.det x') :=
    (LinearMap.isUnit_iff_isUnit_det x').mp
      ((LinearMap.isUnit_iff_ker_eq_bot x').mpr (LinearMap.ker_eq_bot.mpr hx'i))
  have hyu : IsUnit (LinearMap.det y') :=
    (LinearMap.isUnit_iff_isUnit_det y').mp
      ((LinearMap.isUnit_iff_ker_eq_bot y').mpr (LinearMap.ker_eq_bot.mpr hy'i))
  have hcomp : x' ∘ₗ y' = c • (y' ∘ₗ x') := by
    ext w
    simp [x', y', hxy]
  have hdet := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_comp] at hdet
  have h2 : (c ^ finrank K W) * (LinearMap.det y' * LinearMap.det x') =
      1 * (LinearMap.det y' * LinearMap.det x') := by
    linear_combination (-1 : K) * hdet
  exact mul_right_cancel₀ (mul_ne_zero hyu.ne_zero hxu.ne_zero) h2

theorem false_of_pow_five_scalar (W : Submodule K V) (hW0 : 0 < finrank K W)
    (hW5 : finrank K W < 5) (x : V →ₗ[K] V) (hx : ∀ w ∈ W, x w ∈ W) (c : K)
    (hxc : ∀ v, (x ^ 5) v = c • v) (hc : ∀ b : K, b ^ 5 ≠ c) : False := by
  classical
  let x' : W →ₗ[K] W := x.restrict hx
  have hnt : Nontrivial W := Module.finrank_pos_iff.mp hW0
  have hpow : ∀ (n : ℕ) (w : W), (((x' ^ n) w : W) : V) = (x ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      show x (((x' ^ n) w : W) : V) = x ((x ^ n) w)
      rw [ih]
  have hmap : x' ^ 5 = c • (1 : Module.End K W) := by
    ext w
    simp only [LinearMap.smul_apply, Module.End.one_apply]
    rw [hpow, hxc]
    rfl
  have haeval : Polynomial.aeval x' (Polynomial.X ^ 5 - Polynomial.C c) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hmap,
      Module.algebraMap_end_eq_smul_id]
    exact sub_eq_zero.mpr rfl
  have hirr : Irreducible (Polynomial.X ^ 5 - Polynomial.C c) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_five hc
  have hdvd : minpoly K x' ∣ Polynomial.X ^ 5 - Polynomial.C c := minpoly.dvd K x' haeval
  have hdeg : (minpoly K x').natDegree ≤ finrank K W := by
    have h1 := Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly x')
      (LinearMap.charpoly_monic x').ne_zero
    rwa [LinearMap.charpoly_natDegree] at h1
  obtain ⟨r, hr⟩ := hdvd
  rcases hirr.isUnit_or_isUnit hr with hu | hu
  · exact minpoly.not_isUnit K x' hu
  · have h1 : r.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have h2 : (Polynomial.X ^ 5 - Polynomial.C c : Polynomial K).natDegree = 5 :=
      Polynomial.natDegree_X_pow_sub_C
    have h3 : (minpoly K x').natDegree + r.natDegree = 5 := by
      rw [← h2, hr, Polynomial.natDegree_mul (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x'))
        hu.ne_zero]
    omega

theorem not_pow_five_of_primitive {K : Type*} [Field K] [Finite K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) (h25 : ¬ 25 ∣ Nat.card Kˣ) : ∀ b : K, b ^ 5 ≠ ζ := by
  intro b hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hb
    exact hζ.ne_zero (by norm_num) hb.symm
  let u : Kˣ := Units.mk0 b hb0
  have hu5 : (u : K) ^ 5 = ζ := hb
  have h25' : u ^ 25 = 1 := by
    apply Units.ext
    have : (u : K) ^ 25 = ((u : K) ^ 5) ^ 5 := by rw [← pow_mul]
    rw [Units.val_pow_eq_pow_val, this, hu5, hζ.pow_eq_one, Units.val_one]
  have h5ne : u ^ 5 ≠ 1 := by
    intro h
    have : ((u ^ 5 : Kˣ) : K) = 1 := by rw [h]; rfl
    rw [Units.val_pow_eq_pow_val, hu5] at this
    exact hζ.ne_one (by norm_num) this
  have hd : orderOf u ∣ 25 := orderOf_dvd_of_pow_eq_one h25'
  have hd5 : ¬ orderOf u ∣ 5 := fun h => h5ne (orderOf_dvd_iff_pow_eq_one.mp h)
  have : orderOf u = 25 := by
    have h25p : (25 : ℕ) = 5 ^ 2 := by norm_num
    rw [h25p] at hd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hd
    interval_cases k
    · exfalso; exact hd5 (by rw [hk']; norm_num)
    · exfalso; exact hd5 (by rw [hk']; norm_num)
    · rw [hk']; norm_num
  apply h25
  rw [← this]
  exact orderOf_dvd_natCard u

end Comm

end CFSG.RankThree.PartOne.KFU
