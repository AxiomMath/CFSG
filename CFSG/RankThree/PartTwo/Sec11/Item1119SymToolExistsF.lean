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

theorem aux_ExistsF_mem_closure_pair {G : Type*} [Group G] {a d : G} (had : a * d = d * a)
    {f : G} (hf : f ∈ Subgroup.closure ({a, d} : Set G)) :
    ∃ i j : ℤ, f = a ^ i * d ^ j := by
  have hc : Commute a d := had
  have hmul : ∀ x y : G, (∃ i j : ℤ, x = a ^ i * d ^ j) → (∃ i j : ℤ, y = a ^ i * d ^ j) →
      ∃ i j : ℤ, x * y = a ^ i * d ^ j := by
    rintro x y ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    refine ⟨i + k, j + l, ?_⟩
    calc a ^ i * d ^ j * (a ^ k * d ^ l) = a ^ i * (d ^ j * a ^ k) * d ^ l := by
          simp only [mul_assoc]
      _ = a ^ i * (a ^ k * d ^ j) * d ^ l := by
          rw [(hc.symm.zpow_zpow j k).eq]
      _ = a ^ (i + k) * d ^ (j + l) := by
          rw [zpow_add, zpow_add]
          simp only [mul_assoc]
  have hinv : ∀ x : G, (∃ i j : ℤ, x = a ^ i * d ^ j) → ∃ i j : ℤ, x⁻¹ = a ^ i * d ^ j := by
    rintro x ⟨i, j, rfl⟩
    refine ⟨-i, -j, ?_⟩
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact (hc.symm.zpow_zpow (-j) (-i)).eq
  let S : Subgroup G :=
    { carrier := {x | ∃ i j : ℤ, x = a ^ i * d ^ j}
      mul_mem' := fun {x y} hx hy => hmul x y hx hy
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := fun {x} hx => hinv x hx }
  have hle : Subgroup.closure ({a, d} : Set G) ≤ S := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact ⟨1, 0, by simp⟩
    · rw [hx]
      exact ⟨0, 1, by simp⟩
  exact hle hf

theorem aux_ExistsF_zpow_eq_one {G : Type*} [Group G] (B : Subgroup G) {a : G}
    (haB : a ∉ B) (ha3 : a ^ 3 = 1) {i : ℤ} (hi : a ^ i ∈ B) : a ^ i = 1 := by
  have h3 : a ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact ha3
  rw [zpow_eq_zpow_emod i h3] at hi ⊢
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hcases with h | h | h
  · rw [h, zpow_zero]
  · exfalso
    rw [h, zpow_one] at hi
    exact haB hi
  · exfalso
    rw [h, zpow_ofNat] at hi
    have hsq : a = a ^ 2 * a ^ 2 := by
      calc a = a ^ 3 * a := by rw [ha3, one_mul]
        _ = a ^ 2 * a ^ 2 := by group
    have h2 : a ^ 2 * a ^ 2 ∈ B := B.mul_mem hi hi
    rw [← hsq] at h2
    exact haB h2

theorem exists_f_of_card_nine {G : Type*} [Group G] [Finite G] (B : Subgroup G) (a d : G)
    (hB : Nat.card B = 9) (hdB : d ∈ B) (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1)
    (haB : a ∉ B) (ha3 : a ^ 3 = 1) (had : a * d = d * a) :
    ∃ f ∈ B, f ∉ Subgroup.closure ({a, d} : Set G) ∧
      Subgroup.closure ({f, d} : Set G) = B := by
  have hord : orderOf d = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hd3) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hd1
    · exact h
  have hcard_d : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers]
    exact hord
  have hex : ∃ f ∈ B, f ∉ Subgroup.zpowers d := by
    by_contra hcon
    have hle : B ≤ Subgroup.zpowers d := fun x hx => by
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨f, hfB, hfd⟩ := hex
  have hfcl : Subgroup.closure ({f, d} : Set G) ≤ B :=
    (Subgroup.closure_le B).2 (Set.insert_subset hfB (Set.singleton_subset_iff.2 hdB))
  have hdmem : d ∈ Subgroup.closure ({f, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem f (Set.mem_singleton d))
  have hfmem : f ∈ Subgroup.closure ({f, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert f {d})
  have hdcl : Subgroup.zpowers d ≤ Subgroup.closure ({f, d} : Set G) :=
    Subgroup.zpowers_le.2 hdmem
  refine ⟨f, hfB, ?_, ?_⟩
  · intro hf
    obtain ⟨i, j, hij⟩ := aux_ExistsF_mem_closure_pair had hf
    have hai : a ^ i ∈ B := by
      have heq : a ^ i = f * (d ^ j)⁻¹ := by
        rw [hij, mul_inv_cancel_right]
      rw [heq]
      exact B.mul_mem hfB (B.inv_mem (B.zpow_mem hdB j))
    have h1 : a ^ i = 1 := aux_ExistsF_zpow_eq_one B haB ha3 hai
    apply hfd
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨j, by rw [hij, h1, one_mul]⟩
  · set C := Subgroup.closure ({f, d} : Set G)
    have hdvd : Nat.card C ∣ 9 := by
      have h := Subgroup.card_dvd_of_le hfcl
      rwa [hB] at h
    have hge : 3 ≤ Nat.card C := by
      have h := Subgroup.card_le_of_le hdcl
      omega
    have hne : Nat.card C ≠ 3 := by
      intro h3
      have heq : Subgroup.zpowers d = C := Subgroup.eq_of_le_of_card_ge hdcl (by omega)
      exact hfd (by rw [heq]; exact hfmem)
    have h9 : Nat.card C = 9 := by
      obtain ⟨c, hc⟩ : ∃ c, Nat.card C = c := ⟨_, rfl⟩
      rw [hc] at hdvd hge hne ⊢
      have hle9 : c ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases c <;> omega
    exact Subgroup.eq_of_le_of_card_ge hfcl (by omega)

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
