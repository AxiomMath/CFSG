module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType

private lemma natModEq_pow_prime_pow {p : ℕ} (hp : p.Prime) (j m : ℕ) :
    j ^ p ^ m ≡ j [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_pow]
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]

theorem fieldAut_fixes_pow_eq_one {K : Type} [Field K] {p m : ℕ} (hp : p.Prime) {σ : K ≃+* K}
    (hσ : σ ^ p ^ m = 1) {x : K} (hx : x ^ p = 1) : σ x = x := by
  by_cases hx1 : x = 1
  · rw [hx1, map_one]
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hx⟩
    have horder : orderOf x = p := orderOf_eq_prime hx hx1
    have hprim : IsPrimitiveRoot x p := IsPrimitiveRoot.iff_orderOf.mpr horder
    have hσx_pow : (σ x) ^ p = 1 := by rw [← map_pow, hx, map_one]
    obtain ⟨j, _hjlt, hj⟩ := hprim.eq_pow_of_pow_eq_one hσx_pow
    have hpow : ∀ k : ℕ, (σ ^ k) x = x ^ (j ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          calc (σ ^ (k + 1)) x = σ ((σ ^ k) x) := by rw [pow_succ', RingAut.mul_apply]
            _ = σ (x ^ (j ^ k)) := by rw [ih]
            _ = (σ x) ^ (j ^ k) := by rw [map_pow]
            _ = (x ^ j) ^ (j ^ k) := by rw [← hj]
            _ = x ^ (j * j ^ k) := by rw [pow_mul]
            _ = x ^ (j ^ (k + 1)) := by rw [pow_succ']
    have h1 : (σ ^ (p ^ m)) x = x := by rw [hσ]; rfl
    have hxpow : x ^ (j ^ (p ^ m)) = x ^ 1 := by rw [← hpow (p ^ m), h1, pow_one]
    have hmod1 : j ^ (p ^ m) ≡ 1 [MOD p] := by
      have h' : j ^ (p ^ m) ≡ 1 [MOD orderOf x] :=
        (IsOfFinOrder.pow_eq_pow_iff_modEq (x := x) hfin).mp hxpow
      rwa [horder] at h'
    have hfermat : j ^ (p ^ m) ≡ j [MOD p] := natModEq_pow_prime_pow hp j m
    have hjmod : j ≡ 1 [MOD p] := hfermat.symm.trans hmod1
    have hxj : x ^ j = x ^ 1 := by
      have hjmod' : j ≡ 1 [MOD orderOf x] := by rwa [horder]
      exact (IsOfFinOrder.pow_eq_pow_iff_modEq (x := x) hfin).mpr hjmod'
    rw [← hj, hxj, pow_one]

end CFSG.StandardType
