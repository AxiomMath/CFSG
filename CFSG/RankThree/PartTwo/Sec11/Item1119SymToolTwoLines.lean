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

theorem aux_TwoLines_pow_mod {G : Type*} [Group G] (x : G) (hx : x ^ 3 = 1) (n : ℕ) :
    x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem aux_TwoLines_mul3 {G : Type*} [Group G] (x y z : G)
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (i j k i' j' k' : ℕ) :
    x ^ i * y ^ j * z ^ k * (x ^ i' * y ^ j' * z ^ k') =
      x ^ (i + i') * y ^ (j + j') * z ^ (k + k') := by
  have Cxz : Commute (z ^ k) (x ^ i') :=
    (Commute.pow_pow (show Commute x z from hxz) i' k).symm
  have Cyx : Commute (y ^ j) (x ^ i') :=
    (Commute.pow_pow (show Commute x y from hxy) i' j).symm
  have Czy : Commute (z ^ k) (y ^ j') :=
    (Commute.pow_pow (show Commute y z from hyz) j' k).symm
  rw [pow_add, pow_add, pow_add]
  simp only [mul_assoc, Cxz.left_comm, Cyx.left_comm, Czy.left_comm]

theorem aux_TwoLines_normal3 {G : Type*} [Group G] (x y z : G)
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) {w : G}
    (hw : w ∈ Subgroup.closure ({x, y, z} : Set G)) :
    ∃ i j k : ℕ, w = x ^ i * y ^ j * z ^ k := by
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨i, j, k, rfl⟩ := ha
    obtain ⟨i', j', k', rfl⟩ := hb
    exact ⟨i + i', j + j', k + k', aux_TwoLines_mul3 x y z hxy hxz hyz i j k i' j' k'⟩
  | inv a _ ha =>
    obtain ⟨i, j, k, rfl⟩ := ha
    refine ⟨2 * i, 2 * j, 2 * k, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [aux_TwoLines_mul3 x y z hxy hxz hyz i j k (2 * i) (2 * j) (2 * k),
      show i + 2 * i = 3 * i by ring, show j + 2 * j = 3 * j by ring,
      show k + 2 * k = 3 * k by ring, pow_mul, pow_mul, pow_mul, hx3, hy3, hz3]
    simp

theorem aux_TwoLines_pair_eq {G : Type*} [Group G] (u d e : G)
    (hud : u * d = d * u) (hu3 : u ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (he : e ∈ Subgroup.closure ({u, d} : Set G))
    (hed : e ∉ Subgroup.closure ({d} : Set G)) :
    Subgroup.closure ({e, d} : Set G) = Subgroup.closure ({u, d} : Set G) := by
  have hsub : ({u, d} : Set G) ⊆ ({u, d, 1} : Set G) :=
    Set.insert_subset_insert (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  obtain ⟨m, k, hmk⟩ : ∃ m k : ℕ, e = u ^ m * d ^ k := by
    obtain ⟨i, j, l, h⟩ := aux_TwoLines_normal3 u d 1 hud (by simp) (by simp) hu3 hd3
      (by simp) (Subgroup.closure_mono hsub he)
    exact ⟨i, j, by rw [h, one_pow, mul_one]⟩
  have hde : d ∈ Subgroup.closure ({e, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hke : d ^ k ∈ Subgroup.closure ({e, d} : Set G) := pow_mem hde k
  have hum : u ^ m ∈ Subgroup.closure ({e, d} : Set G) := by
    have h1 : e ∈ Subgroup.closure ({e, d} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have h2 : u ^ m = e * (d ^ k)⁻¹ := by rw [hmk, mul_inv_cancel_right]
    rw [h2]
    exact mul_mem h1 (inv_mem hke)
  have hu : u ∈ Subgroup.closure ({e, d} : Set G) := by
    have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hr with h0 | h1 | h2
    · exfalso
      apply hed
      rw [hmk, aux_TwoLines_pow_mod u hu3 m, h0, pow_zero, one_mul]
      exact pow_mem (Subgroup.subset_closure (Set.mem_singleton d)) k
    · have h' : u ^ m = u := by rw [aux_TwoLines_pow_mod u hu3 m, h1, pow_one]
      rw [h'] at hum
      exact hum
    · have h' : u ^ m = u ^ 2 := by rw [aux_TwoLines_pow_mod u hu3 m, h2]
      rw [h'] at hum
      have h4 := pow_mem hum 2
      have h5 : (u ^ 2) ^ 2 = u := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, hu3, one_mul, pow_one]
      rwa [h5] at h4
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact Set.insert_subset_iff.mpr ⟨he, Set.singleton_subset_iff.mpr
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩
  · rw [Subgroup.closure_le]
    exact Set.insert_subset_iff.mpr ⟨hu, Set.singleton_subset_iff.mpr hde⟩

theorem aux_TwoLines_split {G : Type*} [Group G] (a c d w : G)
    (hac : a * c = c * a) (had : a * d = d * a) (hcd : c * d = d * c)
    (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hw : w ∈ Subgroup.closure ({c, a, d} : Set G))
    (hwc : w ∉ Subgroup.closure ({c, d} : Set G))
    (hwa : w ∉ Subgroup.closure ({a, d} : Set G)) :
    w ∈ Subgroup.closure ({a * c, d} : Set G) ∨
      w ∈ Subgroup.closure ({a * c ^ 2, d} : Set G) := by
  have hw' : w ∈ Subgroup.closure ({a, c, d} : Set G) := by
    rwa [Set.insert_comm]
  obtain ⟨i, j, k, rfl⟩ := aux_TwoLines_normal3 a c d hac had hcd ha3 hc3 hd3 hw'
  have hi : a ^ i = a ^ (i % 3) := aux_TwoLines_pow_mod a ha3 i
  have hj : c ^ j = c ^ (j % 3) := aux_TwoLines_pow_mod c hc3 j
  have hi0 : i % 3 ≠ 0 := by
    intro h
    apply hwc
    rw [hi, h, pow_zero, one_mul]
    exact mul_mem (pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) j)
      (pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) k)
  have hj0 : j % 3 ≠ 0 := by
    intro h
    apply hwa
    rw [hj, h, pow_zero, mul_one]
    exact mul_mem (pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) i)
      (pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) k)
  have hi' : i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hj' : j % 3 = 1 ∨ j % 3 = 2 := by omega
  have hac' : Commute a c := hac
  have hu : a * c ∈ Subgroup.closure ({a * c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hd : d ∈ Subgroup.closure ({a * c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hu' : a * c ^ 2 ∈ Subgroup.closure ({a * c ^ 2, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hd' : d ∈ Subgroup.closure ({a * c ^ 2, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hc4 : (c ^ 2) ^ 2 = c := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, hc3, one_mul, pow_one]
  have e21 : a ^ 2 * c = (a * c ^ 2) ^ 2 := by
    rw [(hac'.pow_right 2).mul_pow, hc4]
  rw [hi, hj]
  rcases hi' with h1 | h1 <;> rcases hj' with h2 | h2
  · left
    rw [h1, h2, pow_one, pow_one]
    exact mul_mem hu (pow_mem hd k)
  · right
    rw [h1, h2, pow_one]
    exact mul_mem hu' (pow_mem hd' k)
  · right
    rw [h1, h2, pow_one, e21]
    exact mul_mem (pow_mem hu' 2) (pow_mem hd' k)
  · left
    rw [h1, h2, ← hac'.mul_pow 2]
    exact mul_mem (pow_mem hu 2) (pow_mem hd k)

theorem two_lines_cover {G : Type*} [Group G] [Finite G] (a c d e₀ e₁ z : G)
    (hac : a * c = c * a) (had : a * d = d * a) (hcd : c * d = d * c)
    (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hindep : a ∉ Subgroup.closure ({c, d} : Set G))
    (he₀ : e₀ ∈ Subgroup.closure ({c, a, d} : Set G))
    (he₀c : e₀ ∉ Subgroup.closure ({c, d} : Set G))
    (he₀a : e₀ ∉ Subgroup.closure ({a, d} : Set G))
    (he₁ : e₁ ∈ Subgroup.closure ({c, a, d} : Set G))
    (he₁c : e₁ ∉ Subgroup.closure ({c, d} : Set G))
    (he₁a : e₁ ∉ Subgroup.closure ({a, d} : Set G))
    (hz : z ∈ Subgroup.closure ({c, a, d} : Set G))
    (hzc : z ∉ Subgroup.closure ({c, d} : Set G))
    (hza : z ∉ Subgroup.closure ({a, d} : Set G))
    (hne : Subgroup.closure ({e₀, d} : Set G) ≠ Subgroup.closure ({e₁, d} : Set G)) :
    z ∈ Subgroup.closure ({e₀, d} : Set G) ∨ z ∈ Subgroup.closure ({e₁, d} : Set G) := by
  have hac' : Commute a c := hac
  have had' : Commute a d := had
  have hcd' : Commute c d := hcd
  have hud_p : a * c * d = d * (a * c) := (had'.mul_left hcd').eq
  have hud_m : a * c ^ 2 * d = d * (a * c ^ 2) := (had'.mul_left (hcd'.pow_left 2)).eq
  have hu3p : (a * c) ^ 3 = 1 := by rw [hac'.mul_pow, ha3, hc3, one_mul]
  have hu3m : (a * c ^ 2) ^ 3 = 1 := by
    rw [(hac'.pow_right 2).mul_pow, ha3, one_mul, ← pow_mul, mul_comm, pow_mul, hc3, one_pow]
  have hdle : Subgroup.closure ({d} : Set G) ≤ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.closure_mono
      (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hS : ∀ e : G, e ∈ Subgroup.closure ({c, a, d} : Set G) →
      e ∉ Subgroup.closure ({c, d} : Set G) → e ∉ Subgroup.closure ({a, d} : Set G) →
      Subgroup.closure ({e, d} : Set G) = Subgroup.closure ({a * c, d} : Set G) ∨
        Subgroup.closure ({e, d} : Set G) = Subgroup.closure ({a * c ^ 2, d} : Set G) := by
    intro e he hec hea
    rcases aux_TwoLines_split a c d e hac had hcd ha3 hc3 hd3 he hec hea with h | h
    · exact Or.inl (aux_TwoLines_pair_eq (a * c) d e hud_p hu3p hd3 h
        (fun h' => hec (hdle h')))
    · exact Or.inr (aux_TwoLines_pair_eq (a * c ^ 2) d e hud_m hu3m hd3 h
        (fun h' => hec (hdle h')))
  have hz' := aux_TwoLines_split a c d z hac had hcd ha3 hc3 hd3 hz hzc hza
  rcases hS e₀ he₀ he₀c he₀a with h0 | h0 <;> rcases hS e₁ he₁ he₁c he₁a with h1 | h1
  · exact absurd (h0.trans h1.symm) hne
  · rcases hz' with hz'' | hz''
    · exact Or.inl (by rw [h0]; exact hz'')
    · exact Or.inr (by rw [h1]; exact hz'')
  · rcases hz' with hz'' | hz''
    · exact Or.inr (by rw [h1]; exact hz'')
    · exact Or.inl (by rw [h0]; exact hz'')
  · exact absurd (h0.trans h1.symm) hne

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
