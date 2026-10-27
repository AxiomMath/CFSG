module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem aux_LineEq_mem_form {G : Type*} [Group G] (u d : G) (hud : u * d = d * u) (x : G)
    (hx : x ∈ Subgroup.closure ({u, d} : Set G)) : ∃ a b : ℤ, x = u ^ a * d ^ b := by
  have hcomm : Commute u d := hud
  let S : Subgroup G :=
    { carrier := {x | ∃ a b : ℤ, x = u ^ a * d ^ b}
      mul_mem' := by
        rintro x y ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
        refine ⟨a + c, b + e, ?_⟩
        have hc : d ^ b * u ^ c = u ^ c * d ^ b := (Commute.zpow_zpow hcomm c b).eq.symm
        calc u ^ a * d ^ b * (u ^ c * d ^ e)
            = u ^ a * (d ^ b * u ^ c) * d ^ e := by simp only [mul_assoc]
          _ = u ^ a * (u ^ c * d ^ b) * d ^ e := by rw [hc]
          _ = u ^ (a + c) * d ^ (b + e) := by
            rw [zpow_add, zpow_add]
            simp only [mul_assoc]
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro x ⟨a, b, rfl⟩
        refine ⟨-a, -b, ?_⟩
        rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
        exact (Commute.zpow_zpow hcomm (-a) (-b)).eq.symm }
  have hle : Subgroup.closure ({u, d} : Set G) ≤ S := by
    apply (Subgroup.closure_le _).mpr
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · exact (⟨1, 0, by simp [h]⟩ : ∃ a b : ℤ, y = u ^ a * d ^ b)
    · exact (⟨0, 1, by simp [h]⟩ : ∃ a b : ℤ, y = u ^ a * d ^ b)
  exact hle hx

theorem closure_pair_eq_of_mem {G : Type*} [Group G] [Finite G] (u e d : G)
    (hud : u * d = d * u) (hu3 : u ^ 3 = 1) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hu : u ∉ Subgroup.zpowers d)
    (he : e ∈ Subgroup.closure ({u, d} : Set G)) (hed : e ∉ Subgroup.zpowers d) :
    Subgroup.closure ({e, d} : Set G) = Subgroup.closure ({u, d} : Set G) := by
  have hcomm : Commute u d := hud
  obtain ⟨a, b, rfl⟩ := aux_LineEq_mem_form u d hud e he
  have hu3' : u ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hu3]
  have ha3 : ¬ (3 : ℤ) ∣ a := by
    rintro ⟨q, rfl⟩
    apply hed
    have h1 : u ^ (3 * q) = 1 := by
      rw [zpow_mul, hu3', one_zpow]
    rw [h1, one_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) b
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, 3 * x + a * y = 1 := by
    have h : a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases h with h | h
    · exact ⟨-(a / 3), 1, by omega⟩
    · exact ⟨-(2 * (a / 3) + 1), 2, by omega⟩
  have hu1 : u ^ (a * y) = u := by
    have h2 : a * y = 1 + 3 * (-x) := by linarith
    rw [h2, zpow_add, zpow_mul, hu3', one_zpow, mul_one, zpow_one]
  have hey : (u ^ a * d ^ b) ^ y = u * d ^ (b * y) := by
    rw [(Commute.zpow_zpow hcomm a b).mul_zpow, ← zpow_mul, ← zpow_mul, hu1]
  have hu_eq : u = (u ^ a * d ^ b) ^ y * d ^ (-(b * y)) := by
    rw [hey, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h
    · rw [h]
      exact he
    · rw [h]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h
    · have hmem : (u ^ a * d ^ b) ^ y * d ^ (-(b * y)) ∈
          Subgroup.closure ({u ^ a * d ^ b, d} : Set G) :=
        Subgroup.mul_mem _
          (Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) y)
          (Subgroup.zpow_mem _
            (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _)
      rw [← hu_eq] at hmem
      rw [h]
      exact hmem
    · rw [h]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem map_conj_closure_pair {G : Type*} [Group G] (n c d : G)
    (hnd : Subgroup.zpowers (n * d * n⁻¹) = Subgroup.zpowers d) :
    (Subgroup.closure ({c, d} : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.closure ({n * c * n⁻¹, d} : Set G) := by
  have h1 : (MulAut.conj n).toMonoidHom c = n * c * n⁻¹ := rfl
  have h2 : (MulAut.conj n).toMonoidHom d = n * d * n⁻¹ := rfl
  rw [MonoidHom.map_closure, Set.image_pair, h1, h2]
  have hd_self : d ∈ Subgroup.closure ({n * c * n⁻¹, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hw : n * d * n⁻¹ ∈ Subgroup.zpowers d := by
    rw [← hnd]
    exact Subgroup.mem_zpowers _
  have hd' : d ∈ Subgroup.zpowers (n * d * n⁻¹) := by
    rw [hnd]
    exact Subgroup.mem_zpowers _
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [h]
      exact Subgroup.zpowers_le.mpr hd_self hw
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [h]
      exact Subgroup.zpowers_le.mpr
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hd'

theorem exists_pow_orderOf_eq_three {G : Type*} [Group G] (z : G) (hz1 : z ≠ 1)
    (hz : ∃ k : ℕ, z ^ 3 ^ k = 1) : ∃ m : ℕ, orderOf (z ^ m) = 3 := by
  obtain ⟨k, hk⟩ := hz
  have hdvd : orderOf z ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hz1
    rw [← orderOf_eq_one_iff, hi, pow_zero]
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  refine ⟨3 ^ j, ?_⟩
  have hdvd2 : 3 ^ j ∣ orderOf z := by
    rw [hi]
    exact pow_dvd_pow 3 (Nat.le_succ j)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num : (3 : ℕ) ≠ 0)) hdvd2, hi, pow_succ,
    Nat.mul_div_cancel_left _ (pow_pos (by norm_num : (0 : ℕ) < 3) j)]

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
