module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.Timmesfeld.Bridge

namespace RootOne

theorem orderOf_lt_card {A : Type*} [AddCommGroup A] [Finite A] [Nontrivial A]
    (h2 : ∀ a : A, a + a = 0) (f : AddMonoid.End A) : orderOf f < Nat.card A := by
  classical
  rcases Nat.eq_zero_or_pos (orderOf f) with h0 | hpos
  · rw [h0]
    exact Nat.card_pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Module (ZMod 2) A :=
    AddCommGroup.zmodModule (n := 2) (fun a => by rw [two_nsmul]; exact h2 a)
  have : Module.Finite (ZMod 2) A := Module.Finite.of_finite
  set r := Module.finrank (ZMod 2) A with hr
  set L : Module.End (ZMod 2) A := (f : A →+ A).toZModLinearMap 2 with hL
  have hLpow : ∀ (k : ℕ) (a : A), (L ^ k) a = (f ^ k) a := by
    intro k a
    rw [Module.End.pow_apply, AddMonoid.End.coe_pow]
    induction k generalizing a with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      rfl
  set W := Submodule.span (ZMod 2) (Set.range fun i : Fin r => L ^ (i : ℕ)) with hW
  have hgen : ∀ i < r, L ^ i ∈ W := fun i hi => Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have hLr : L ^ r ∈ W := by
    have hCH := LinearMap.aeval_self_charpoly L
    have hmon := LinearMap.charpoly_monic L
    have hdeg : L.charpoly.natDegree = r := LinearMap.charpoly_natDegree L
    rw [hmon.as_sum, hdeg, map_add, map_pow, Polynomial.aeval_X, map_sum] at hCH
    have h1 : L ^ r = -∑ i ∈ Finset.range r,
        (Polynomial.aeval L) (Polynomial.C (L.charpoly.coeff i) * Polynomial.X ^ i) :=
      eq_neg_of_add_eq_zero_left hCH
    rw [h1]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hgen i (Finset.mem_range.1 hi))
  have hLW : ∀ w ∈ W, L * w ∈ W := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨i, hi⟩, rfl⟩ := hw
      rw [← pow_succ']
      rcases Nat.lt_or_ge (i + 1) r with h | h
      · exact hgen _ h
      · rw [show i + 1 = r by omega]
        exact hLr
    | zero => rw [mul_zero]; exact W.zero_mem
    | add u v _ _ hu hv => rw [mul_add]; exact W.add_mem hu hv
    | smul c u _ hu => rw [mul_smul_comm]; exact W.smul_mem c hu
  have hrpos : 0 < r := Module.finrank_pos
  have hpow : ∀ k : ℕ, L ^ k ∈ W := by
    intro k
    induction k with
    | zero => exact hgen 0 hrpos
    | succ k ih => rw [pow_succ']; exact hLW _ ih
  have hcardW : Nat.card W ≤ 2 ^ r := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have := finrank_range_le_card (R := ZMod 2) (fun i : Fin r => L ^ (i : ℕ))
    rwa [Fintype.card_fin] at this
  have hcardA : Nat.card A = 2 ^ r := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  set m := orderOf f with hm
  have hinj : Function.Injective fun k : Fin m => (⟨L ^ (k : ℕ), hpow k⟩ : W) := by
    intro i j hij
    have h1 : L ^ (i : ℕ) = L ^ (j : ℕ) := congrArg Subtype.val hij
    have h2 : f ^ (i : ℕ) = f ^ (j : ℕ) := by
      ext a
      rw [← hLpow, ← hLpow, h1]
    exact Fin.ext (pow_injOn_Iio_orderOf (Set.mem_Iio.2 i.2) (Set.mem_Iio.2 j.2) h2)
  have hne : ∀ k : Fin m, (⟨L ^ (k : ℕ), hpow k⟩ : W) ≠ 0 := by
    intro k hk
    have h1 : L ^ (k : ℕ) = 0 := congrArg Subtype.val hk
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    have h2 : (f ^ (m - k + k)) a = 0 := by
      rw [pow_add]
      change (f ^ (m - k)) ((f ^ (k : ℕ)) a) = 0
      rw [← hLpow k, h1, LinearMap.zero_apply, map_zero]
    rw [Nat.sub_add_cancel k.2.le, pow_orderOf_eq_one] at h2
    exact ha h2
  have hle : m + 1 ≤ Nat.card W := by
    have : Finite W := Module.finite_of_finite (ZMod 2)
    let g : Option (Fin m) → W := fun o => o.elim 0 fun k => ⟨L ^ (k : ℕ), hpow k⟩
    have hg : Function.Injective g := by
      rintro (_ | i) (_ | j) hij
      · rfl
      · exact absurd hij.symm (hne j)
      · exact absurd hij (hne i)
      · exact congrArg some (hinj hij)
    have h1 := Nat.card_le_card_of_injective g hg
    rwa [Finite.card_option, Nat.card_fin] at h1
  omega

end RootOne

end CFSG.Timmesfeld.Bridge
