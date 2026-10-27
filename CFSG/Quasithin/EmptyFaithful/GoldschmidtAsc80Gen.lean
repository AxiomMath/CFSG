module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix

theorem commutator_le_of_relIndex_eq_two {G : Type*} [Group G] {H N : Subgroup G}
    (h : H.relIndex N = 2) : ⁅N, N⁆ ≤ H := by
  have hi : (H.subgroupOf N).index = 2 := h
  have : (H.subgroupOf N).Normal := Subgroup.normal_of_index_eq_two hi
  have hcard : Nat.card (N ⧸ H.subgroupOf N) = 2 := by
    rw [← Subgroup.index.eq_1, hi]
  have : Fact (Nat.Prime (Nat.card (N ⧸ H.subgroupOf N))) := ⟨hcard ▸ Nat.prime_two⟩
  have : IsCyclic (N ⧸ H.subgroupOf N) := isCyclic_of_prime_card rfl
  have hcomm : ∀ a b : N ⧸ H.subgroupOf N, a * b = b * a :=
    (IsCyclic.commGroup (α := N ⧸ H.subgroupOf N)).mul_comm
  rw [Subgroup.commutator_le]
  intro g hg k hk
  have key : (⟨g, hg⟩ : N) * ⟨k, hk⟩ * (⟨g, hg⟩ : N)⁻¹ * (⟨k, hk⟩ : N)⁻¹ ∈ H.subgroupOf N := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact mul_inv_eq_one.mpr (mul_inv_eq_iff_eq_mul.mpr (hcomm _ _))
  exact key

theorem cube_root_ne {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {i r : F} (hi : i ^ 2 = -1)
    (hr : r ^ 3 = 1) : r ≠ -1 ∧ r ≠ i ∧ r ≠ -i := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at hr
    exact h2 (by linear_combination -hr)
  · rw [h] at hr
    exact h2 (by linear_combination (1 - (i - 1) * i) * hi + (i - 1) * hr)
  · rw [h] at hr
    exact h2 (by linear_combination (1 - (i + 1) * i) * hi - (i + 1) * hr)

theorem offdiag_zero_of_scalar_commute {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {i r : F}
    (hi : i ^ 2 = -1) (hr : r ^ 3 = 1) {g : Matrix (Fin 3) (Fin 3) F}
    (h : Matrix.scalar (Fin 3) r * Matrix.diagonal ![i, -i, 1] * g =
      g * Matrix.diagonal ![i, -i, 1]) :
    g 0 1 = 0 ∧ g 0 2 = 0 ∧ g 1 0 = 0 ∧ g 1 2 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0 := by
  obtain ⟨hr1, hr2, hr3⟩ := cube_root_ne h2 hi hr
  have hi0 : i ≠ 0 := fun h0 => by
    rw [h0] at hi
    simp at hi
  have key : ∀ x c : F, x * c = 0 → c ≠ 0 → x = 0 := fun x c h hc =>
    (mul_eq_zero.mp h).resolve_right hc
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  have e10 := congrFun (congrFun h 1) 0
  have e12 := congrFun (congrFun h 1) 2
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    at e01 e02 e10 e12 e20 e21
  refine ⟨key _ (-i - r * i) (by linear_combination -e01) fun h0 => hr1 ?_,
    key _ (1 - r * i) (by linear_combination -e02) fun h0 => hr3 ?_,
    key _ (i + r * i) (by linear_combination -e10) fun h0 => hr1 ?_,
    key _ (1 + r * i) (by linear_combination -e12) fun h0 => hr2 ?_,
    key _ (i - r) (by linear_combination -e20) fun h0 => hr2 ?_,
    key _ (-i - r) (by linear_combination -e21) fun h0 => hr3 ?_⟩
  · have : (-i) * (r + 1) = 0 := by linear_combination h0
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr hi0))
  · linear_combination i * h0 + r * hi
  · have : i * (r + 1) = 0 := by linear_combination h0
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_left hi0)
  · linear_combination -i * h0 + r * hi
  · linear_combination -h0
  · linear_combination -h0

theorem diag_mul_eq {R : Type*} [CommRing R] {a a' c : R} (hinv : a' * a = 1) (hc : c = a')
    {g : Matrix (Fin 3) (Fin 3) R} (h02 : g 0 2 = 0) (h12 : g 1 2 = 0) (h20 : g 2 0 = 0)
    (h21 : g 2 1 = 0) (h00 : g 0 0 = 0) (h11 : g 1 1 = 0) :
    Matrix.diagonal ![a, 1, c] * g =
      Matrix.diagonal ![a, a', 1] * g * Matrix.diagonal ![a, 1, c] := by
  subst hc
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, h02, h12, h20, h21, h00, h11]
  · linear_combination (-g 1 0) * hinv
  · ring

end CFSG.Quasithin.E2P.Asc80
