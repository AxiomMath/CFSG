module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

theorem aux_Numbers_zpow_natpow3 {G : Type} [Group G] (x : G) (k : ℤ) :
    (x ^ k) ^ 3 = x ^ (k * 3) := by
  rw [← zpow_natCast, ← zpow_mul] <;> norm_num

theorem aux_Numbers_natpow3_zpow {G : Type} [Group G] (x : G) (k : ℤ) :
    (x ^ 3) ^ k = x ^ (3 * k) := by
  rw [← zpow_natCast, ← zpow_mul] <;> norm_num

theorem aux_Numbers_zpow_pow_three {G : Type} [Group G] {c : G} (hc3 : c ^ 3 = 1) (n : ℤ) :
    (c ^ n) ^ 3 = 1 := by
  have h3 : c ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact hc3
  calc (c ^ n) ^ 3 = c ^ (n * 3) := aux_Numbers_zpow_natpow3 c n
    _ = c ^ (3 * n) := by rw [mul_comm n 3]
    _ = (c ^ (3 : ℤ)) ^ n := zpow_mul c 3 n
    _ = 1 := by rw [h3, one_zpow]

theorem exists_zpow_form {G : Type} [Group G] {r c a : G} (hrc : r * c = c * r)
    (ha : a ∈ Subgroup.closure ({r, c} : Set G)) : ∃ j n : ℤ, a = r ^ j * c ^ n := by
  have hcomm : Commute r c := hrc
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨j1, n1, rfl⟩ := ihx
    obtain ⟨j2, n2, rfl⟩ := ihy
    have hc : c ^ n1 * r ^ j2 = r ^ j2 * c ^ n1 := (hcomm.symm.zpow_zpow n1 j2).eq
    refine ⟨j1 + j2, n1 + n2, ?_⟩
    calc r ^ j1 * c ^ n1 * (r ^ j2 * c ^ n2)
        = r ^ j1 * (c ^ n1 * r ^ j2) * c ^ n2 := by simp only [mul_assoc]
      _ = r ^ j1 * (r ^ j2 * c ^ n1) * c ^ n2 := by rw [hc]
      _ = r ^ (j1 + j2) * c ^ (n1 + n2) := by
        rw [zpow_add r j1 j2, zpow_add c n1 n2]
        simp only [mul_assoc]
  | inv x _ ihx =>
    obtain ⟨j, n, rfl⟩ := ihx
    refine ⟨-j, -n, ?_⟩
    have hc : c ^ (-n) * r ^ (-j) = r ^ (-j) * c ^ (-n) :=
      (hcomm.symm.zpow_zpow (-n) (-j)).eq
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact hc

theorem closure_pair_eq_of_zpowers_eq {G : Type} [Group G] (r s c : G)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c) :
    Subgroup.closure ({r, s} : Set G) = Subgroup.closure ({r, c} : Set G) := by
  have hr_rc : r ∈ Subgroup.closure ({r, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert r {c})
  have hc_rc : c ∈ Subgroup.closure ({r, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem r (Set.mem_singleton c))
  have hr_rs : r ∈ Subgroup.closure ({r, s} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert r {s})
  have hs_rs : s ∈ Subgroup.closure ({r, s} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem r (Set.mem_singleton s))
  have hs_rc : s ∈ Subgroup.closure ({r, c} : Set G) := by
    have h1 : s ∈ Subgroup.zpowers c := by
      rw [← hs]
      exact Subgroup.mem_zpowers s
    exact Subgroup.zpowers_le.mpr hc_rc h1
  have hc_rs : c ∈ Subgroup.closure ({r, s} : Set G) := by
    have h1 : c ∈ Subgroup.zpowers s := by
      rw [hs]
      exact Subgroup.mem_zpowers c
    exact Subgroup.zpowers_le.mpr hs_rs h1
  apply le_antisymm
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hr_rc, hs_rc⟩
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hr_rs, hc_rs⟩

theorem r_mem_closure_of_pow_three_eq_one {G : Type} [Group G] {r c a : G}
    (hrc : r * c = c * r) (hr3 : r ^ 3 = 1)
    (ha : a ∈ Subgroup.closure ({r, c} : Set G)) (hac : a ∉ Subgroup.zpowers c) :
    r ∈ Subgroup.closure ({a, c} : Set G) := by
  obtain ⟨j, n, hjn⟩ := exists_zpow_form hrc ha
  have hr3z : r ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact hr3
  have hred : ∀ k : ℤ, r ^ k = r ^ (k % 3) := by
    intro k
    have hk : r ^ k = r ^ (k % 3 + 3 * (k / 3)) := by
      congr 1
      omega
    rw [hk, zpow_add, zpow_mul, hr3z, one_zpow, mul_one]
  have ha_mem : a ∈ Subgroup.closure ({a, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert a {c})
  have hc_mem : c ∈ Subgroup.closure ({a, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton c))
  have hrj : r ^ j ∈ Subgroup.closure ({a, c} : Set G) := by
    have heq : r ^ j = a * c ^ (-n) := by
      rw [hjn, mul_assoc, ← zpow_add]
      simp
    rw [heq]
    exact mul_mem ha_mem (Subgroup.zpow_mem _ hc_mem (-n))
  have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    apply hac
    rw [hjn, hred j, h0, zpow_zero, one_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) n
  · have hrj' : r ^ j = r := by
      rw [hred j, h1, zpow_one]
    rw [hrj'] at hrj
    exact hrj
  · have hr : r = (r ^ j) ^ (2 : ℤ) := by
      rw [← zpow_mul, hred (j * 2)]
      have h12 : j * 2 % 3 = 1 := by omega
      rw [h12, zpow_one]
    rw [hr]
    exact Subgroup.zpow_mem _ hrj 2

theorem closure_eq_of_pow_three_eq_one {G : Type} [Group G] {r c a s : G}
    (hrc : r * c = c * r) (hr3 : r ^ 3 = 1) (hs : Subgroup.zpowers s = Subgroup.zpowers c)
    (ha : a ∈ Subgroup.closure ({r, c} : Set G)) (hac : a ∉ Subgroup.zpowers c) :
    Subgroup.closure ({r, s} : Set G) = Subgroup.closure ({a, s} : Set G) := by
  have hr' : r ∈ Subgroup.closure ({a, c} : Set G) :=
    r_mem_closure_of_pow_three_eq_one hrc hr3 ha hac
  have hc_ac : c ∈ Subgroup.closure ({a, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton c))
  have hc_rc : c ∈ Subgroup.closure ({r, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem r (Set.mem_singleton c))
  rw [closure_pair_eq_of_zpowers_eq r s c hs, closure_pair_eq_of_zpowers_eq a s c hs]
  apply le_antisymm
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hr', hc_ac⟩
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨ha, hc_rc⟩

theorem cube_facts_of_orderOf_nine {G : Type} [Group G] {r c a : G}
    (hrc : r * c = c * r) (hc3 : c ^ 3 = 1) (ha3 : a ^ 3 = 1) (hr9 : orderOf r = 9)
    (ha : a ∈ Subgroup.closure ({r, c} : Set G)) (hac : a ∉ Subgroup.zpowers c) :
    r ^ 3 ∈ Subgroup.closure ({a, c} : Set G) ∧ r ^ 3 ∉ Subgroup.zpowers c := by
  have hcomm : Commute r c := hrc
  obtain ⟨j, n, hjn⟩ := exists_zpow_form hrc ha
  have hcomm_rj_cn : Commute (r ^ j) (c ^ n) := hcomm.zpow_zpow j n
  have hrj3 : (r ^ j) ^ 3 = 1 := by
    have h := ha3
    rw [hjn, hcomm_rj_cn.mul_pow 3, aux_Numbers_zpow_pow_three hc3 n, mul_one] at h
    exact h
  have hrj3' : r ^ (j * 3) = 1 :=
    (aux_Numbers_zpow_natpow3 r j).symm.trans hrj3
  have hdvd : ((orderOf r : ℕ) : ℤ) ∣ j * 3 := orderOf_dvd_iff_zpow_eq_one.mpr hrj3'
  rw [hr9] at hdvd
  have hdvd' : (9 : ℤ) ∣ j * 3 := by exact_mod_cast hdvd
  obtain ⟨m, hm⟩ : ∃ m : ℤ, j = 3 * m := ⟨j / 3, by omega⟩
  have hA : a = (r ^ 3) ^ m * c ^ n := by
    rw [hjn, hm, aux_Numbers_natpow3_zpow]
  have ht_mem : r ^ 3 ∈ Subgroup.closure ({r ^ 3, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hc_mem : c ∈ Subgroup.closure ({r ^ 3, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have ha' : a ∈ Subgroup.closure ({r ^ 3, c} : Set G) := by
    rw [hA]
    exact mul_mem (Subgroup.zpow_mem _ ht_mem m) (Subgroup.zpow_mem _ hc_mem n)
  have hrc3 : r ^ 3 * c = c * r ^ 3 := (hcomm.pow_left 3).eq
  have hr3' : (r ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]
    have h9 : r ^ orderOf r = 1 := pow_orderOf_eq_one r
    rw [hr9] at h9
    exact h9
  have key : r ^ 3 ∈ Subgroup.closure ({a, c} : Set G) :=
    r_mem_closure_of_pow_three_eq_one hrc3 hr3' ha' hac
  refine ⟨key, ?_⟩
  intro hmem
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  apply hac
  rw [hA, ← hl, ← zpow_mul, ← zpow_add]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
