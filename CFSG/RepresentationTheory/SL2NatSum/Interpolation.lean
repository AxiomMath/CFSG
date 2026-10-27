module

public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.PolyIndep

public section

namespace CFSG.RepresentationTheory.SL2NatSum

variable {K : Type*} [Field K] [Fintype K] {M : Type*} [AddCommGroup M] [Module K M]

theorem coeff_eq_zero_of_forall_sum_eq_zero (c : ℕ → M)
    (h : ∀ x : K, ∑ j ∈ Finset.range (Fintype.card K), x ^ j • c j = 0) :
    ∀ j < Fintype.card K, c j = 0 := by
  intro j hj
  have hmem : c j ∈ (⊥ : Submodule K M) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.mem_of_forall_poly_finset
      (⊥ : Submodule K M) (Finset.range (Fintype.card K))
      (fun e he => Finset.mem_range.mp he) c (fun x => by simpa using h x)
      j (Finset.mem_range.mpr hj)
  simpa using hmem

private lemma sum_Ico_pow_mul_pow [DecidableEq K] {x y : K} (hy : y ≠ 0) :
    (∑ j ∈ Finset.Ico 1 (Fintype.card K),
        x ^ j * y ^ (Fintype.card K - 1 - j)) = if x = y then -1 else 0 := by
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have hx : x ≠ 0 := hy
    calc
      (∑ j ∈ Finset.Ico 1 (Fintype.card K), x ^ j * x ^ (Fintype.card K - 1 - j))
          = ∑ _j ∈ Finset.Ico 1 (Fintype.card K), x ^ (Fintype.card K - 1) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [← pow_add]
            congr 1
            have h1 := (Finset.mem_Ico.mp hj).1
            have h2 := (Finset.mem_Ico.mp hj).2
            omega
      _ = ((Finset.Ico 1 (Fintype.card K)).card : K) * x ^ (Fintype.card K - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = (((Fintype.card K - 1 : ℕ) : K)) * 1 := by
            rw [Nat.card_Ico, FiniteField.pow_card_sub_one_eq_one x hx]
      _ = -1 := by
            have hq : 1 ≤ Fintype.card K := Fintype.card_pos
            rw [Nat.cast_sub hq, FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub,
              mul_one]
  · rw [if_neg hxy]
    have hmul := (Commute.all x y).geom_sum₂_Ico_mul (m := 1) (n := Fintype.card K)
      (by have := Fintype.card_pos (α := K); omega)
    have hpow : y ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one y hy
    have hxq : x ^ Fintype.card K = x := FiniteField.pow_card x
    have hzero : (∑ j ∈ Finset.Ico 1 (Fintype.card K),
        x ^ j * y ^ (Fintype.card K - 1 - j)) * (x - y) = 0 := by
      rw [hmul, hxq, hpow, pow_one, one_mul, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hxy)

private noncomputable def lagrangeCoeff (f : K → M) : ℕ → M :=
  fun j => if j = 0 then 0 else
    (-1 : K) • ∑ y : K, y ^ (Fintype.card K - 1 - j) • f y

private lemma sum_Ico_lagrangeCoeff (f : K → M) {x : K} (hx : x ≠ 0) :
    ∑ j ∈ Finset.Ico 1 (Fintype.card K), x ^ j • lagrangeCoeff f j =
      (-1 : K) • ∑ y : K,
        (∑ j ∈ Finset.Ico 1 (Fintype.card K),
          x ^ j * y ^ (Fintype.card K - 1 - j)) • f y := by
  classical
  calc
    ∑ j ∈ Finset.Ico 1 (Fintype.card K), x ^ j • lagrangeCoeff f j
        = ∑ j ∈ Finset.Ico 1 (Fintype.card K),
            (-1 : K) • ∑ y : K,
              (x ^ j * y ^ (Fintype.card K - 1 - j)) • f y := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj0 : j ≠ 0 := by have := (Finset.mem_Ico.mp hj).1; omega
          dsimp only [lagrangeCoeff]
          rw [if_neg hj0, smul_comm (x ^ j) (-1), Finset.smul_sum]
          congr 1
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [smul_smul]
    _ = (-1 : K) • ∑ y : K, ∑ j ∈ Finset.Ico 1 (Fintype.card K),
          (x ^ j * y ^ (Fintype.card K - 1 - j)) • f y := by
          rw [← Finset.smul_sum]
          congr 1
          rw [Finset.sum_comm]
    _ = (-1 : K) • ∑ y : K,
          (∑ j ∈ Finset.Ico 1 (Fintype.card K),
            x ^ j * y ^ (Fintype.card K - 1 - j)) • f y := by
          congr 1
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_smul]

theorem exists_coeff (f : K → M) (hf : f 0 = 0) :
    ∃ c : ℕ → M, c 0 = 0 ∧ ∀ x : K, f x = ∑ j ∈ Finset.range (Fintype.card K), x ^ j • c j := by
  classical
  refine ⟨lagrangeCoeff f, by simp [lagrangeCoeff], fun x => ?_⟩
  have hqpos : 0 < Fintype.card K := Fintype.card_pos
  by_cases hx : x = 0
  · subst hx
    rw [hf]
    symm
    refine Finset.sum_eq_zero fun j hj => ?_
    by_cases hj0 : j = 0
    · subst hj0
      simp [lagrangeCoeff]
    · rw [zero_pow hj0, zero_smul]
  · have hsplit : ∑ j ∈ Finset.range (Fintype.card K), x ^ j • lagrangeCoeff f j =
        ∑ j ∈ Finset.Ico 1 (Fintype.card K), x ^ j • lagrangeCoeff f j := by
      rw [Finset.range_eq_Ico]
      rw [show Finset.Ico 0 (Fintype.card K) = insert 0 (Finset.Ico 1 (Fintype.card K)) by
        ext j
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega,
        Finset.sum_insert (by simp)]
      simp [lagrangeCoeff]
    have hterm : ∀ y : K,
        (∑ j ∈ Finset.Ico 1 (Fintype.card K),
          x ^ j * y ^ (Fintype.card K - 1 - j)) • f y =
          if y = x then (-1 : K) • f x else 0 := by
      intro y
      by_cases hyx : y = x
      · subst y
        rw [if_pos rfl, sum_Ico_pow_mul_pow (x := x) (y := x) hx, if_pos rfl]
      · rw [if_neg hyx]
        by_cases hy0 : y = 0
        · subst hy0
          rw [hf, smul_zero]
        · rw [sum_Ico_pow_mul_pow (x := x) (y := y) hy0, if_neg (Ne.symm hyx),
            zero_smul]
    have hsum : ∑ j ∈ Finset.range (Fintype.card K), x ^ j • lagrangeCoeff f j =
        (-1 : K) • ∑ y : K,
          (∑ j ∈ Finset.Ico 1 (Fintype.card K),
            x ^ j * y ^ (Fintype.card K - 1 - j)) • f y := by
      rw [hsplit, sum_Ico_lagrangeCoeff f hx]
    calc
      f x = (-1 : K) • ((-1 : K) • f x) := by simp
      _ = (-1 : K) • ∑ y : K,
            (∑ j ∈ Finset.Ico 1 (Fintype.card K),
              x ^ j * y ^ (Fintype.card K - 1 - j)) • f y := by
            congr 1
            rw [Finset.sum_congr rfl fun y _ => hterm y]
            simp
      _ = ∑ j ∈ Finset.range (Fintype.card K), x ^ j • lagrangeCoeff f j := hsum.symm

theorem coeff₂_eq_zero_of_forall_sum_eq_zero (c : ℕ → ℕ → M)
    (h : ∀ x y : K, ∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
      x ^ i • y ^ k • c i k = 0) :
    ∀ i < Fintype.card K, ∀ k < Fintype.card K, c i k = 0 := by
  intro i hi k hk
  have hd : ∀ y : K, ∀ i < Fintype.card K,
      ∑ k ∈ Finset.range (Fintype.card K), y ^ k • c i k = 0 := by
    intro y i hi
    refine coeff_eq_zero_of_forall_sum_eq_zero
      (fun i => ∑ k ∈ Finset.range (Fintype.card K), y ^ k • c i k) (fun x => ?_) i hi
    rw [← h x y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
  exact coeff_eq_zero_of_forall_sum_eq_zero (fun k => c i k) (fun y => hd y i hi) k hk

end CFSG.RepresentationTheory.SL2NatSum
