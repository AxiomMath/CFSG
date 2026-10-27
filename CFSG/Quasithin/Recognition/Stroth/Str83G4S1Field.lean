module

public import TauCeti.FieldTheory.Finite.MinpolyOrbit

public section

namespace CFSG.Quasithin.Stroth

open Polynomial

private theorem map_pow_mul_eq {K : Type} [Field K] (f : K →+ K) {μ ν : K}
    (h : ∀ u, f (μ * u) = ν * f u) (k : ℕ) (u : K) : f (μ ^ k * u) = ν ^ k * f u := by
  induction k generalizing u with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, h, ih, ← mul_assoc, pow_succ']

private theorem map_algebraMap_mul {K : Type} [Field K] [Algebra (ZMod 2) K] (f : K →+ K)
    (c : ZMod 2) (x : K) :
    f (algebraMap (ZMod 2) K c * x) = algebraMap (ZMod 2) K c * f x := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, c = k := ⟨c.val, (ZMod.natCast_zmod_val c).symm⟩
  rw [map_natCast, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

private theorem map_aeval_mul_eq {K : Type} [Field K] [Algebra (ZMod 2) K] (f : K →+ K) {μ ν : K}
    (h : ∀ u, f (μ * u) = ν * f u) (p : (ZMod 2)[X]) (u : K) :
    f (aeval μ p * u) = aeval ν p * f u := by
  induction p using Polynomial.induction_on' generalizing u with
  | add p q hp hq => simp only [map_add, add_mul, hp, hq]
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, mul_assoc, map_algebraMap_mul, map_pow_mul_eq f h,
      mul_assoc]

theorem eq_one_of_injective_map_mul_eq_inv_sq {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : Odd n) (hK : Nat.card K = 2 ^ n) (f : K →+ K)
    (hf : Function.Injective f) {μ : K} (hμ : μ ≠ 0)
    (h : ∀ u, f (μ * u) = (μ ^ 2)⁻¹ * f u) : μ = 1 := by
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hint : IsIntegral (ZMod 2) μ := (Algebra.IsAlgebraic.isAlgebraic (R := ZMod 2) μ).isIntegral
  have hf1 : f 1 ≠ 0 := fun h0 => one_ne_zero (hf (h0.trans f.map_zero.symm))
  have hroot : aeval (μ ^ 2)⁻¹ (minpoly (ZMod 2) μ) = 0 := by
    have := map_aeval_mul_eq f h (minpoly (ZMod 2) μ) 1
    rw [minpoly.aeval, zero_mul, map_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_right hf1
  have hmin : minpoly (ZMod 2) (μ ^ 2)⁻¹ = minpoly (ZMod 2) μ :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hroot
      (minpoly.monic hint)).symm
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨j, hj⟩ := (TauCeti.FiniteField.mem_orbit_iff_exists_pow_card_pow (ZMod 2)).1
    ((TauCeti.FiniteField.mem_orbit_iff_minpoly_eq (ZMod 2)).2 hmin)
  rw [ZMod.card] at hj
  have hfrob : μ ^ 2 ^ n = μ := by
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card μ
  obtain ⟨m, hmμ⟩ : ∃ m : Kˣ, (m : K) = μ := ⟨Units.mk0 μ hμ, rfl⟩
  have hm1 : m ^ 2 ^ j = (m ^ 2)⁻¹ := Units.ext (by simp [hmμ, hj])
  have hm2 : m ^ 2 ^ n = m := Units.ext (by simp [hmμ, hfrob])
  have hmod1 : (2 : ℤ) ^ j ≡ -2 [ZMOD orderOf m] := by
    have : m ^ ((2 ^ j : ℕ) : ℤ) = m ^ (-2 : ℤ) := by
      rw [zpow_natCast, hm1, zpow_neg, zpow_ofNat]
    exact_mod_cast zpow_eq_zpow_iff_modEq.1 this
  have hmod2 : (2 : ℤ) ^ n ≡ 1 [ZMOD orderOf m] := by
    have : m ^ ((2 ^ n : ℕ) : ℤ) = m ^ (1 : ℤ) := by
      rw [zpow_natCast, hm2, zpow_one]
    exact_mod_cast zpow_eq_zpow_iff_modEq.1 this
  have key : (1 : ℤ) ≡ -1 [ZMOD orderOf m] :=
    calc (1 : ℤ) = 1 ^ j := (one_pow j).symm
      _ ≡ ((2 : ℤ) ^ n) ^ j [ZMOD orderOf m] := (hmod2.pow j).symm
      _ = ((2 : ℤ) ^ j) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≡ (-2) ^ n [ZMOD orderOf m] := hmod1.pow n
      _ = -(2 ^ n) := hn.neg_pow 2
      _ ≡ -1 [ZMOD orderOf m] := hmod2.neg
  have hdvd : orderOf m ∣ 2 := by
    have h2 := Int.modEq_iff_dvd.1 key
    rw [show (-1 : ℤ) - 1 = -2 by norm_num, dvd_neg] at h2
    exact_mod_cast h2
  have hμ2 : μ ^ 2 = 1 := by
    have := congrArg Units.val (orderOf_dvd_iff_pow_eq_one.1 hdvd)
    simpa [hmμ] using this
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (μ - 1) ^ 2 = 0 := by linear_combination hμ2 + (1 - μ) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsq)

end CFSG.Quasithin.Stroth

end
