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

namespace CFSG.RankThree.PartTwo.Sec11

theorem sym1119_comm_cube_mem {G : Type*} [Group G] {A : Subgroup G} {x g : G}
    (hord : orderOf x = 27)
    (hA3 : ∀ u ∈ A, u ^ 3 = 1)
    (hyA : ∀ u ∈ A, u * x ^ 3 = x ^ 3 * u)
    (h9A : x ^ 9 ∈ A) (hg9 : g * x ^ 9 = x ^ 9 * g)
    (hW : ∃ (i : ℤ) (u : G), u ∈ A ∧ (x ^ 3)⁻¹ * (g⁻¹ * x ^ 3 * g) = (x ^ 3) ^ i * u) :
    (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g ∈ A := by
  obtain ⟨i, u, hu, hW'⟩ := hW
  have h3dvd : (3 : ℕ) ∣ orderOf x := ⟨9, by omega⟩
  have hordy : orderOf (x ^ 3) = 9 := by
    rw [orderOf_pow_of_dvd (by norm_num : (3 : ℕ) ≠ 0) h3dvd, hord] <;> norm_num
  have hz : g⁻¹ * x ^ 3 * g = (x ^ 3) ^ (1 + i) * u := by
    calc g⁻¹ * x ^ 3 * g = x ^ 3 * ((x ^ 3)⁻¹ * (g⁻¹ * x ^ 3 * g)) :=
          (mul_inv_cancel_left _ _).symm
      _ = x ^ 3 * ((x ^ 3) ^ i * u) := by rw [hW']
      _ = (x ^ 3) ^ (1 + i) * u := by rw [zpow_one_add, mul_assoc]
  have hconj : ∀ (y : G) (n : ℕ), (g⁻¹ * y * g) ^ n = g⁻¹ * y ^ n * g := by
    intro y n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc, mul_inv_cancel_left]
  have h39 : (x ^ 3) ^ 3 = x ^ 9 := by
    rw [← pow_mul] <;> norm_num
  have hgx9 : g⁻¹ * x ^ 9 * g = x ^ 9 := by
    rw [mul_assoc, ← hg9, inv_mul_cancel_left]
  have hcube : (g⁻¹ * x ^ 3 * g) ^ 3 = x ^ 9 := by
    rw [hconj (x ^ 3) 3, h39, hgx9]
  have hcu : Commute (x ^ 3) u := (hyA u hu).symm
  have hcw : Commute ((x ^ 3) ^ (1 + i)) u := hcu.zpow_left (1 + i)
  have hcube' : ((x ^ 3) ^ (1 + i)) ^ 3 = x ^ 9 := by
    rw [hz, hcw.mul_pow 3, hA3 u hu, mul_one] at hcube
    exact hcube
  have e1 : (x ^ 3) ^ (3 * (1 + i)) = (x ^ 3) ^ ((3 : ℕ) : ℤ) := by
    calc (x ^ 3) ^ (3 * (1 + i)) = ((x ^ 3) ^ (1 + i)) ^ ((3 : ℕ) : ℤ) := by
          rw [← zpow_mul]; congr 1; push_cast; ring
      _ = ((x ^ 3) ^ (1 + i)) ^ 3 := zpow_natCast _ 3
      _ = x ^ 9 := hcube'
      _ = (x ^ 3) ^ 3 := h39.symm
      _ = (x ^ 3) ^ ((3 : ℕ) : ℤ) := (zpow_natCast _ 3).symm
  have key : (x ^ 3) ^ (3 * i) = 1 := by
    have e2 : (x ^ 3) ^ (3 * i) = (x ^ 3) ^ (3 * (1 + i)) * ((x ^ 3) ^ ((3 : ℕ) : ℤ))⁻¹ := by
      rw [← zpow_sub]; congr 1; push_cast; ring
    rw [e2, e1, mul_inv_cancel]
  have hdvd : ((orderOf (x ^ 3) : ℕ) : ℤ) ∣ 3 * i := orderOf_dvd_iff_zpow_eq_one.mpr key
  rw [hordy] at hdvd
  have hdvd' : (9 : ℤ) ∣ 3 * i := by exact_mod_cast hdvd
  obtain ⟨k, hk⟩ : ∃ k : ℤ, i = 3 * k := ⟨i / 3, by omega⟩
  have h33 : (x ^ 3) ^ (3 : ℤ) = x ^ 9 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, h39]
  have hmem : (x ^ 3) ^ i ∈ A := by
    rw [hk, zpow_mul, h33]
    exact A.zpow_mem h9A k
  have hsplit : (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g = (x ^ 3)⁻¹ * (g⁻¹ * x ^ 3 * g) := by
    simp only [mul_assoc]
  rw [hsplit, hW']
  exact A.mul_mem hmem hu

theorem sym1119_le_of_two_gens {G : Type*} [Group G] [Finite G] {B C : Subgroup G} {d f : G}
    (hcard : Nat.card B = 9) (hd : d ∈ B) (hf : f ∈ B) (hd3 : orderOf d = 3)
    (hfd : f ∉ Subgroup.zpowers d) (hdC : d ∈ C) (hfC : f ∈ C) : B ≤ C := by
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = Subgroup.closure ({d, f} : Set G) := ⟨_, rfl⟩
  have hdK : d ∈ K := by
    rw [hK]
    exact Subgroup.subset_closure (Set.mem_insert d {f})
  have hfK : f ∈ K := by
    rw [hK]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem d (Set.mem_singleton f))
  have hKB : K ≤ B := by
    rw [hK, Subgroup.closure_le]
    exact Set.insert_subset_iff.mpr ⟨hd, Set.singleton_subset_iff.mpr hf⟩
  have hKC : K ≤ C := by
    rw [hK, Subgroup.closure_le]
    exact Set.insert_subset_iff.mpr ⟨hdC, Set.singleton_subset_iff.mpr hfC⟩
  have hzK : Subgroup.zpowers d ≤ K := Subgroup.zpowers_le.mpr hdK
  have hcardz : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers]
    exact hd3
  have hdvdB : Nat.card K ∣ 9 := by
    have h := Subgroup.card_dvd_of_le hKB
    rw [hcard] at h
    exact h
  have hdvdK : 3 ∣ Nat.card K := by
    have h := Subgroup.card_dvd_of_le hzK
    rw [hcardz] at h
    exact h
  have hle9 : Nat.card K ≤ 9 := Nat.le_of_dvd (by norm_num) hdvdB
  have key : ∀ n : ℕ, n ∣ 9 → 3 ∣ n → n ≤ 9 → n = 3 ∨ n = 9 := by
    intro n h1 h2 h3
    interval_cases n <;> first | omega | simp_all
  rcases key _ hdvdB hdvdK hle9 with h3 | h9
  · exfalso
    have heq : Subgroup.zpowers d = K := Subgroup.eq_of_le_of_card_ge hzK (by omega)
    exact hfd (by rw [heq]; exact hfK)
  · have heq : K = B := Subgroup.eq_of_le_of_card_ge hKB (by omega)
    rw [← heq]
    exact hKC

theorem sym1119_mem_zpowers_zpow {G : Type*} [Group G] {d : G} (hd3 : d ^ 3 = 1) {κ : ℤ}
    (hκ : ¬ (3 : ℤ) ∣ κ) : d ∈ Subgroup.zpowers (d ^ κ) := by
  have hd3' : d ^ (3 : ℤ) = 1 := by exact_mod_cast hd3
  have hr : κ * κ % 3 = 1 := by
    have h1 : κ % 3 = 1 ∨ κ % 3 = 2 := by omega
    rcases h1 with h | h <;> rw [Int.mul_emod, h] <;> norm_num
  have hmem : (d ^ κ) ^ κ = d := by
    rw [← zpow_mul, zpow_eq_zpow_emod (κ * κ) hd3', hr, zpow_one]
  have h := Subgroup.zpow_mem (Subgroup.zpowers (d ^ κ)) (Subgroup.mem_zpowers (d ^ κ)) κ
  rw [hmem] at h
  exact h

end CFSG.RankThree.PartTwo.Sec11

end
