module

public import CFSG.LocalAnalysis.StandardType.GGTorusScalar
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType.TorC

open CFSG.StandardType CFSG.StandardType.SpJoin

@[expose] def rootC (n m : ℕ) :
    (Fin n → Multiplicative (ZMod m)) →* (Fin n → Multiplicative (ZMod m)) where
  toFun c k := if h : k.val + 1 < n then c k * (c ⟨k.val + 1, h⟩)⁻¹ else c k ^ 2
  map_one' := by
    funext k
    by_cases h : k.val + 1 < n <;> simp [h]
  map_mul' c d := by
    funext k
    change (if h : k.val + 1 < n then (c * d) k * ((c * d) ⟨k.val + 1, h⟩)⁻¹
        else (c * d) k ^ 2) =
      (if h : k.val + 1 < n then c k * (c ⟨k.val + 1, h⟩)⁻¹ else c k ^ 2) *
        (if h : k.val + 1 < n then d k * (d ⟨k.val + 1, h⟩)⁻¹ else d k ^ 2)
    by_cases h : k.val + 1 < n
    · simp only [dif_pos h, Pi.mul_apply]
      rw [mul_inv]
      ac_rfl
    · simp only [dif_neg h, Pi.mul_apply]
      rw [mul_pow]

theorem rootC_apply_of_lt {n m : ℕ} (c : Fin n → Multiplicative (ZMod m)) (k : Fin n)
    (h : k.val + 1 < n) : rootC n m c k = c k * (c ⟨k.val + 1, h⟩)⁻¹ := by
  simp [rootC, h]

theorem rootC_apply_of_not_lt {n m : ℕ} (c : Fin n → Multiplicative (ZMod m)) (k : Fin n)
    (h : ¬ k.val + 1 < n) : rootC n m c k = c k ^ 2 := by
  simp [rootC, h]

@[expose] def corC (n m : ℕ) (k : Fin n) :
    Multiplicative (ZMod m) →* (Fin n → Multiplicative (ZMod m)) where
  toFun z := if h : k.val + 1 < n then Pi.mulSingle k z * Pi.mulSingle ⟨k.val + 1, h⟩ z⁻¹
    else Pi.mulSingle k z
  map_one' := by
    funext i
    by_cases h : k.val + 1 < n <;> simp [h]
  map_mul' z w := by
    by_cases h : k.val + 1 < n
    · simp only [dif_pos h, Pi.mulSingle_mul, Pi.mulSingle_inv]
      rw [mul_inv]
      ac_rfl
    · simp only [dif_neg h, Pi.mulSingle_mul]

theorem corC_apply_of_lt_eq {n m : ℕ} (k : Fin n) (h : k.val + 1 < n)
    (z : Multiplicative (ZMod m)) (i : Fin n) :
    corC n m k z i =
      if i = k then z else if i = ⟨k.val + 1, h⟩ then z⁻¹ else 1 := by
  rw [show corC n m k z = Pi.mulSingle k z * Pi.mulSingle ⟨k.val + 1, h⟩ z⁻¹ by
    simp [corC, h]]
  by_cases h1 : i = k
  · rw [if_pos h1]
    have hne : k ≠ ⟨k.val + 1, h⟩ := by
      intro hh
      have := congrArg Fin.val hh
      simp at this
    rw [h1, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne]
    simp
  · by_cases h2 : i = ⟨k.val + 1, h⟩
    · rw [if_neg h1, if_pos h2]
      have hne : ⟨k.val + 1, h⟩ ≠ k := by
        intro hh
        have := congrArg Fin.val hh
        simp at this
      rw [h2, Pi.mul_apply, Pi.mulSingle_eq_of_ne hne, Pi.mulSingle_eq_same]
      simp
    · rw [if_neg h1, if_neg h2, Pi.mul_apply, Pi.mulSingle_eq_of_ne h1,
          Pi.mulSingle_eq_of_ne h2]
      simp

theorem corC_apply_of_not_lt_eq {n m : ℕ} (k : Fin n) (h : ¬ k.val + 1 < n)
    (z : Multiplicative (ZMod m)) (i : Fin n) :
    corC n m k z i = if i = k then z else 1 := by
  rw [show corC n m k z = Pi.mulSingle k z by simp [corC, h]]
  by_cases h1 : i = k
  · subst h1; simp
  · rw [Pi.mulSingle_eq_of_ne h1]
    simp [h1]

theorem eq_one_of_sq_eq_one_of_odd {m : ℕ} (hm : Odd m)
    {z : Multiplicative (ZMod m)} (hz : z ^ 2 = 1) : z = 1 := by
  let y : ZMod m := Multiplicative.toAdd z
  have hy : (2 : ZMod m) * y = 0 := by
    have h := congrArg Multiplicative.toAdd hz
    simpa [y, pow_two, two_mul] using h
  have hunit : IsUnit (2 : ZMod m) :=
    (ZMod.isUnit_iff_coprime 2 m).mpr (Nat.coprime_two_left.mpr hm)
  have hy0 : y = 0 := (hunit.mul_right_eq_zero).mp hy
  simpa [y] using congrArg Multiplicative.ofAdd hy0

theorem rootC_corC {n m : ℕ} (k : Fin n) (z : Multiplicative (ZMod m)) :
    rootC n m (corC n m k z) = corTuple (CartanMatrix.C n).transpose k z := by
  funext j
  by_cases hk : k.val + 1 < n
  · by_cases hj : j.val + 1 < n
    · rw [rootC_apply_of_lt _ _ hj, corC_apply_of_lt_eq k hk z,
        corC_apply_of_lt_eq k hk z]
      simp only [corTuple_apply, Matrix.transpose_apply, CartanMatrix.C, Matrix.of_apply,
        Fin.ext_iff]
      split_ifs <;> first | omega | simp [pow_two]
    · rw [rootC_apply_of_not_lt _ _ hj, corC_apply_of_lt_eq k hk z]
      simp only [corTuple_apply, Matrix.transpose_apply, CartanMatrix.C, Matrix.of_apply,
        Fin.ext_iff]
      split_ifs <;> first | omega | simp [pow_two]
  · by_cases hj : j.val + 1 < n
    · rw [rootC_apply_of_lt _ _ hj, corC_apply_of_not_lt_eq k hk z,
        corC_apply_of_not_lt_eq k hk z]
      simp only [corTuple_apply, Matrix.transpose_apply, CartanMatrix.C, Matrix.of_apply,
        Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · rw [rootC_apply_of_not_lt _ _ hj, corC_apply_of_not_lt_eq k hk z]
      simp only [corTuple_apply, Matrix.transpose_apply, CartanMatrix.C, Matrix.of_apply,
        Fin.ext_iff]
      split_ifs <;> first | omega | simp [pow_two]

theorem spRefl_eq_mul_corC {n m : ℕ} (k : Fin n) (c : Fin n → Multiplicative (ZMod m)) :
    spRefl n m k c = c * (corC n m k (rootC n m c k))⁻¹ := by
  funext i
  by_cases hk : k.val + 1 < n
  · rw [spRefl, dif_pos hk, rootC_apply_of_lt c k hk, Pi.mul_apply, Pi.inv_apply,
      corC_apply_of_lt_eq k hk]
    have hne : k ≠ ⟨k.val + 1, hk⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    by_cases h1 : i = k
    · rw [h1]
      simp [Equiv.swap_apply_left]
    · by_cases h2 : i = ⟨k.val + 1, hk⟩
      · rw [h2]
        have hne' : ⟨k.val + 1, hk⟩ ≠ k := by
          intro hh
          have := congrArg Fin.val hh
          simp at this
        simp [Equiv.swap_apply_right, hne']
      · have hswap : Equiv.swap k ⟨k.val + 1, hk⟩ i = i := by
          rw [Equiv.swap_apply_def]
          simp [h1, h2]
        simp [hswap, h1, h2]
  · rw [spRefl, dif_neg hk, rootC_apply_of_not_lt c k hk, Pi.mul_apply, Pi.inv_apply,
      corC_apply_of_not_lt_eq k hk]
    by_cases h1 : i = k
    · subst h1
      simp [sq]
    · simp [h1]

theorem rootC_injective {n m : ℕ} (hm : Odd m) : Function.Injective (rootC n m) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  rcases n with _ | n
  · funext j
    exact Fin.elim0 j
  · have hlast : c (Fin.last n) = 1 := by
      have h := congrFun hc (Fin.last n)
      rw [rootC_apply_of_not_lt c (Fin.last n) (by simp)] at h
      simpa using eq_one_of_sq_eq_one_of_odd hm h
    have hstep : ∀ (j : Fin (n + 1)) (hj : j.val + 1 < n + 1),
        c j = c ⟨j.val + 1, hj⟩ := by
      intro j hj
      have h := congrFun hc j
      rw [rootC_apply_of_lt c j hj, Pi.one_apply] at h
      exact mul_inv_eq_one.mp h
    have hdown : ∀ d : ℕ, ∀ j : Fin (n + 1), n - j.val = d → c j = 1 := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro j hj
        by_cases hlt : j.val + 1 < n + 1
        · rw [hstep j hlt]
          exact ih (n - (j.val + 1)) (by omega) ⟨j.val + 1, hlt⟩ rfl
        · have hjlast : j.val = n := by omega
          have hjeq : j = Fin.last n := Fin.ext hjlast
          rw [hjeq]
          exact hlast
    funext j
    exact hdown (n - j.val) j rfl

end CFSG.StandardType.TorC

end
