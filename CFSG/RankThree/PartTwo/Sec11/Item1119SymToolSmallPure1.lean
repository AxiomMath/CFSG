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

theorem aux_SmallPure1_pow_mod3 {G : Type*} [Group G] (w : G) (hw : w ^ 3 = 1) (n : ℕ) :
    w ^ n = w ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hw, one_pow, one_mul]

theorem aux_SmallPure1_zpow_mod3 {G : Type*} [Group G] (d : G) (hd : d ^ 3 = 1) (k : ℤ) :
    d ^ k = d ^ (k % 3) := by
  have hk : d ^ k = d ^ (k % 3 + 3 * (k / 3)) := by
    congr 1
    omega
  rw [hk, zpow_add, zpow_mul, zpow_ofNat, hd, one_zpow, mul_one]

theorem aux_SmallPure1_closure_pair_subset {G : Type*} [Group G] (u v : G)
    (huv : Commute u v) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) :
    ∀ g ∈ Subgroup.closure ({u, v} : Set G), ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ g = u ^ i * v ^ j := by
  have key : ∀ a b c d : ℕ, u ^ a * v ^ b * (u ^ c * v ^ d) = u ^ (a + c) * v ^ (b + d) := by
    intro a b c d
    have hc : v ^ b * u ^ c = u ^ c * v ^ b := (huv.pow_pow c b).eq.symm
    calc u ^ a * v ^ b * (u ^ c * v ^ d) = u ^ a * (v ^ b * u ^ c) * v ^ d := by
          simp only [mul_assoc]
      _ = u ^ a * (u ^ c * v ^ b) * v ^ d := by rw [hc]
      _ = u ^ (a + c) * v ^ (b + d) := by simp only [pow_add, mul_assoc]
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
    · exact ⟨0, 1, by norm_num, by norm_num, by simp⟩
  | one => exact ⟨0, 0, by norm_num, by norm_num, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, hi, hj, rfl⟩ := hx
    obtain ⟨k, l, hk, hl, rfl⟩ := hy
    refine ⟨(i + k) % 3, (j + l) % 3, Nat.mod_lt _ (by norm_num),
      Nat.mod_lt _ (by norm_num), ?_⟩
    rw [key, aux_SmallPure1_pow_mod3 u hu (i + k), aux_SmallPure1_pow_mod3 v hv (j + l)]
  | inv x _ hx =>
    obtain ⟨i, j, hi, hj, rfl⟩ := hx
    refine ⟨(2 * i) % 3, (2 * j) % 3, Nat.mod_lt _ (by norm_num),
      Nat.mod_lt _ (by norm_num), ?_⟩
    apply inv_eq_of_mul_eq_one_right
    have e1 : u ^ (i + (2 * i) % 3) = 1 := by
      rw [aux_SmallPure1_pow_mod3 u hu, show (i + (2 * i) % 3) % 3 = 0 by omega, pow_zero]
    have e2 : v ^ (j + (2 * j) % 3) = 1 := by
      rw [aux_SmallPure1_pow_mod3 v hv, show (j + (2 * j) % 3) % 3 = 0 by omega, pow_zero]
    rw [key, e1, e2, mul_one]

theorem aux_SmallPure1_card_pair_le_nine {G : Type*} [Group G] (u v : G)
    (huv : Commute u v) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) :
    Nat.card (Subgroup.closure ({u, v} : Set G)) ≤ 9 := by
  have hsub := aux_SmallPure1_closure_pair_subset u v huv hu hv
  have hu_mem : u ∈ Subgroup.closure ({u, v} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert u _)
  have hv_mem : v ∈ Subgroup.closure ({u, v} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem u (Set.mem_singleton v))
  let F : Fin 3 × Fin 3 → Subgroup.closure ({u, v} : Set G) := fun p =>
    ⟨u ^ (p.1 : ℕ) * v ^ (p.2 : ℕ), mul_mem (pow_mem hu_mem _) (pow_mem hv_mem _)⟩
  have hF : Function.Surjective F := by
    rintro ⟨g, hg⟩
    obtain ⟨i, j, hi, hj, rfl⟩ := hsub _ hg
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩
  have h := Nat.card_le_card_of_surjective F hF
  simpa using h

theorem aux_SmallPure1_absurd {G : Type*} [Group G] [Finite G] (c a d p q : G)
    (hpq : Commute p q) (hp : p ^ 3 = 1) (hq : q ^ 3 = 1)
    (h27 : Nat.card (Subgroup.closure ({c, a, d} : Set G)) = 27)
    (hsub : ({c, a, d} : Set G) ⊆ Subgroup.closure ({p, q} : Set G)) : False := by
  have hle : Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.closure ({p, q} : Set G) :=
    (Subgroup.closure_le _).mpr hsub
  have h1 := Subgroup.card_le_of_le hle
  have h2 := aux_SmallPure1_card_pair_le_nine p q hpq hp hq
  omega

theorem zpowers_eq_of_orderOf {G : Type*} [Group G] (x d : G) (hx : orderOf x = 27)
    (hd : d ∈ Subgroup.zpowers x) (hd3 : orderOf d = 3) :
    Subgroup.zpowers d = Subgroup.zpowers (x ^ 9) := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  have hpow : (x ^ i) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (x ^ i)
    rwa [hd3] at h
  have hxi : x ^ (i * 3) = 1 := by
    rw [zpow_mul, zpow_ofNat]
    exact hpow
  have hdvd : (27 : ℤ) ∣ i * 3 := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr hxi
    rw [hx] at h
    exact_mod_cast h
  obtain ⟨k, hk⟩ : ∃ k : ℤ, i = 9 * k := ⟨i / 9, by omega⟩
  have hmem : x ^ i ∈ Subgroup.zpowers (x ^ 9) := by
    rw [hk, zpow_mul, zpow_ofNat]
    exact zpow_mem (Subgroup.mem_zpowers _) k
  have hle : Subgroup.zpowers (x ^ i) ≤ Subgroup.zpowers (x ^ 9) :=
    Subgroup.zpowers_le.mpr hmem
  have h9 : orderOf (x ^ 9) = 3 := by
    have h := orderOf_pow_of_dvd (x := x) (n := 9) (by norm_num) (by rw [hx]; norm_num)
    omega
  have hc1 : Nat.card (Subgroup.zpowers (x ^ i)) = 3 := by
    rw [Nat.card_zpowers, hd3]
  have hc2 : Nat.card (Subgroup.zpowers (x ^ 9)) = 3 := by
    rw [Nat.card_zpowers, h9]
  haveI : Finite (Subgroup.zpowers (x ^ 9)) :=
    Nat.finite_of_card_ne_zero (by rw [hc2]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

theorem independence_of_card {G : Type*} [Group G] [Finite G] (a c d : G)
    (hac : a * c = c * a) (had : a * d = d * a) (hcd : c * d = d * c)
    (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (h27 : Nat.card (Subgroup.closure ({c, a, d} : Set G)) = 27) :
    a ∉ Subgroup.zpowers c ∧ c ∉ Subgroup.zpowers d ∧ a ∉ Subgroup.zpowers d ∧
    (∀ z ∈ Subgroup.closure ({a, c} : Set G), z ∈ Subgroup.zpowers d → z = 1) ∧
    a ∉ Subgroup.closure ({c, d} : Set G) ∧ c ∉ Subgroup.closure ({a, d} : Set G) ∧
    d ∉ Subgroup.closure ({a, c} : Set G) := by
  have h5 : a ∉ Subgroup.closure ({c, d} : Set G) := by
    intro h
    refine aux_SmallPure1_absurd c a d c d hcd hc3 hd3 h27 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact Subgroup.subset_closure (Set.mem_insert c _)
    · rw [hx]; exact h
    · rw [hx]; exact Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d))
  have h6 : c ∉ Subgroup.closure ({a, d} : Set G) := by
    intro h
    refine aux_SmallPure1_absurd c a d a d had ha3 hd3 h27 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact h
    · rw [hx]; exact Subgroup.subset_closure (Set.mem_insert a _)
    · rw [hx]; exact Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton d))
  have h7 : d ∉ Subgroup.closure ({a, c} : Set G) := by
    intro h
    refine aux_SmallPure1_absurd c a d a c hac ha3 hc3 h27 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton c))
    · rw [hx]; exact Subgroup.subset_closure (Set.mem_insert a _)
    · rw [hx]; exact h
  have h1 : a ∉ Subgroup.zpowers c := by
    intro h
    apply h5
    have hle : Subgroup.zpowers c ≤ Subgroup.closure ({c, d} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c _))
    exact hle h
  have h2 : c ∉ Subgroup.zpowers d := by
    intro h
    apply h6
    have hle : Subgroup.zpowers d ≤ Subgroup.closure ({a, d} : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton d)))
    exact hle h
  have h3 : a ∉ Subgroup.zpowers d := by
    intro h
    apply h5
    have hle : Subgroup.zpowers d ≤ Subgroup.closure ({c, d} : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d)))
    exact hle h
  have h4 : ∀ z ∈ Subgroup.closure ({a, c} : Set G), z ∈ Subgroup.zpowers d → z = 1 := by
    intro z hz hzd
    by_contra hz1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzd
    have hmod := aux_SmallPure1_zpow_mod3 d hd3 k
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h0 | h0
    · exact hz1 (by rw [← hk, hmod, h0, zpow_zero])
    · apply h7
      have hzd' : z = d := by rw [← hk, hmod, h0, zpow_one]
      rw [← hzd']
      exact hz
    · apply h7
      have hz2 : z = d * d := by rw [← hk, hmod, h0, zpow_ofNat, pow_two]
      have hd3' : d * (d * d) = 1 := by rw [← pow_three]; exact hd3
      have hzz : z * z = d := by
        rw [hz2]
        calc d * d * (d * d) = d * (d * (d * d)) := by simp only [mul_assoc]
          _ = d * 1 := by rw [hd3']
          _ = d := mul_one d
      rw [← hzz]
      exact mul_mem hz hz
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
