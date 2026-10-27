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

namespace CFSG.Quasithin

theorem closure_subset_of_right_closed {G : Type*} [Group G] {S P : Set G}
    (hord : ∀ s ∈ S, ∃ n : ℕ, 0 < n ∧ s ^ n = 1) (h1 : (1 : G) ∈ P)
    (hmul : ∀ p ∈ P, ∀ s ∈ S, p * s ∈ P) : ↑(Subgroup.closure S) ⊆ P := by
  intro g hg
  induction hg using Subgroup.closure_induction_right with
  | one => exact h1
  | mul_right p hp s hs ih => exact hmul p ih s hs
  | mul_inv_cancel p hp s hs ih =>
    obtain ⟨n, hn, hsn⟩ := hord s hs
    have hinv : s⁻¹ = s ^ (n - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hn, hsn]
    have key : ∀ k : ℕ, p * s ^ k ∈ P := by
      intro k
      induction k with
      | zero => simpa using ih
      | succ k ihk =>
        rw [pow_succ, ← mul_assoc]
        exact hmul _ ihk s hs
    rw [hinv]
    exact key _

structure OvergroupData (G : Type*) [Group G] (ι κ : Type*) where
  a : G
  b : G
  s : G
  x : G
  y : G
  gen : Subgroup.closure ({a, b, s, x, y} : Set G) = ⊤
  ha : a ^ 4 = 1
  hb : b ^ 4 = 1
  hs : s ^ 2 = 1
  hx : x ^ 3 = 1
  hy : y ^ 3 = 1
  Tel : ι → G
  i0 : ι
  Tel_zero : Tel i0 = 1
  Tel_mem : ∀ i, Tel i ∈ Subgroup.closure ({a, b, s} : Set G)
  Tel_next : ∀ i, (∃ j, Tel i * a = Tel j) ∧ (∃ j, Tel i * b = Tel j) ∧ (∃ j, Tel i * s = Tel j)
  D : κ → G
  j0 : κ
  ja : κ
  jb : κ
  D_zero : D j0 = 1
  decX : ∀ j i, ∃ k i₁ i₂, D j * Tel i * x = Tel i₁ * D k * Tel i₂
  decY : ∀ j i, ∃ k i₁ i₂, D j * Tel i * y = Tel i₁ * D k * Tel i₂
  decXA : ∀ j, (j = j0 ∨ j = ja) → ∀ i, ∃ k, (k = j0 ∨ k = ja) ∧
    ∃ i₁ i₂, D j * Tel i * x = Tel i₁ * D k * Tel i₂
  decYB : ∀ j, (j = j0 ∨ j = jb) → ∀ i, ∃ k, (k = j0 ∨ k = jb) ∧
    ∃ i₁ i₂, D j * Tel i * y = Tel i₁ * D k * Tel i₂
  D_ja : D ja ∈ Subgroup.closure ({a, b, s, x} : Set G)
  D_jb : D jb ∈ Subgroup.closure ({a, b, s, y} : Set G)
  genA : x ∈ Subgroup.closure ({a, b, s, D ja} : Set G)
  genB : y ∈ Subgroup.closure ({a, b, s, D jb} : Set G)
  genO : ∀ j, j ≠ j0 → j ≠ ja → j ≠ jb →
    x ∈ Subgroup.closure ({a, b, s, D j} : Set G) ∧ y ∈ Subgroup.closure ({a, b, s, D j} : Set G)
  sepA : ∀ i, Tel i ≠ D ja
  sepB : ∀ i, Tel i ≠ D jb
  sepAB : ∀ i₁ i₂, Tel i₁ * D ja * Tel i₂ ≠ D jb

namespace OvergroupData

variable {G ι κ : Type*} [Group G] (d : OvergroupData G ι κ)

@[expose] def T : Subgroup G := Subgroup.closure {d.a, d.b, d.s}

@[expose] def A : Subgroup G := Subgroup.closure {d.a, d.b, d.s, d.x}

@[expose] def B : Subgroup G := Subgroup.closure {d.a, d.b, d.s, d.y}

theorem T_le_A : d.T ≤ d.A :=
  Subgroup.closure_mono fun g hg => by
    rcases hg with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))

theorem T_le_B : d.T ≤ d.B :=
  Subgroup.closure_mono fun g hg => by
    rcases hg with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))

theorem a_mem_T : d.a ∈ d.T := Subgroup.subset_closure (Or.inl rfl)

theorem b_mem_T : d.b ∈ d.T := Subgroup.subset_closure (Or.inr (Or.inl rfl))

theorem s_mem_T : d.s ∈ d.T := Subgroup.subset_closure (Or.inr (Or.inr rfl))

theorem x_mem_A : d.x ∈ d.A :=
  Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))

theorem y_mem_B : d.y ∈ d.B :=
  Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))

theorem mem_T_iff (g : G) : g ∈ d.T ↔ ∃ i, d.Tel i = g := by
  constructor
  · intro hg
    refine closure_subset_of_right_closed (S := {d.a, d.b, d.s}) (P := Set.range d.Tel) ?_
      ⟨d.i0, d.Tel_zero⟩ ?_ hg
    · rintro s (rfl | rfl | rfl)
      · exact ⟨4, by norm_num, d.ha⟩
      · exact ⟨4, by norm_num, d.hb⟩
      · exact ⟨2, by norm_num, d.hs⟩
    · rintro _ ⟨i, rfl⟩ s (rfl | rfl | rfl)
      · exact (d.Tel_next i).1.imp fun j hj => hj.symm
      · exact (d.Tel_next i).2.1.imp fun j hj => hj.symm
      · exact (d.Tel_next i).2.2.imp fun j hj => hj.symm
  · rintro ⟨i, rfl⟩
    exact d.Tel_mem i

theorem Tel_mem_T (i : ι) : d.Tel i ∈ d.T := d.Tel_mem i

theorem exists_Tel_mul (i j : ι) : ∃ k, d.Tel k = d.Tel i * d.Tel j :=
  (d.mem_T_iff _).1 (d.T.mul_mem (d.Tel_mem_T i) (d.Tel_mem_T j))

theorem exists_Tel_inv (i : ι) : ∃ k, d.Tel k = (d.Tel i)⁻¹ :=
  (d.mem_T_iff _).1 (d.T.inv_mem (d.Tel_mem_T i))

theorem next_aux {i₁ i₂ k : ι} {j : κ} {z : G} (hk : d.Tel i₂ * z = d.Tel k) :
    d.Tel i₁ * d.D j * d.Tel i₂ * z = d.Tel i₁ * d.D j * d.Tel k := by
  rw [mul_assoc (d.Tel i₁ * d.D j) (d.Tel i₂) z, hk]

theorem dec_aux {i₁ i₂ i₃ i₄ m : ι} {j k : κ} {z : G}
    (h : d.D j * d.Tel i₂ * z = d.Tel i₃ * d.D k * d.Tel i₄) (hm : d.Tel m = d.Tel i₁ * d.Tel i₃) :
    d.Tel i₁ * d.D j * d.Tel i₂ * z = d.Tel m * d.D k * d.Tel i₄ := by
  calc d.Tel i₁ * d.D j * d.Tel i₂ * z = d.Tel i₁ * (d.D j * d.Tel i₂ * z) := by
        simp only [mul_assoc]
    _ = d.Tel i₁ * (d.Tel i₃ * d.D k * d.Tel i₄) := by rw [h]
    _ = d.Tel m * d.D k * d.Tel i₄ := by rw [hm]; simp only [mul_assoc]

theorem cover (g : G) : ∃ j i₁ i₂, g = d.Tel i₁ * d.D j * d.Tel i₂ := by
  have hg : g ∈ Subgroup.closure ({d.a, d.b, d.s, d.x, d.y} : Set G) := by rw [d.gen]; trivial
  refine closure_subset_of_right_closed (S := {d.a, d.b, d.s, d.x, d.y})
    (P := {g | ∃ j i₁ i₂, g = d.Tel i₁ * d.D j * d.Tel i₂}) ?_ ?_ ?_ hg
  · rintro s (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨4, by norm_num, d.ha⟩
    · exact ⟨4, by norm_num, d.hb⟩
    · exact ⟨2, by norm_num, d.hs⟩
    · exact ⟨3, by norm_num, d.hx⟩
    · exact ⟨3, by norm_num, d.hy⟩
  · exact ⟨d.j0, d.i0, d.i0, by rw [d.Tel_zero, d.D_zero]; simp⟩
  · rintro _ ⟨j, i₁, i₂, rfl⟩ s (rfl | rfl | rfl | rfl | rfl)
    · obtain ⟨k, hk⟩ := (d.Tel_next i₂).1
      exact ⟨j, i₁, k, d.next_aux hk⟩
    · obtain ⟨k, hk⟩ := (d.Tel_next i₂).2.1
      exact ⟨j, i₁, k, d.next_aux hk⟩
    · obtain ⟨k, hk⟩ := (d.Tel_next i₂).2.2
      exact ⟨j, i₁, k, d.next_aux hk⟩
    · obtain ⟨k, i₃, i₄, h⟩ := d.decX j i₂
      obtain ⟨m, hm⟩ := d.exists_Tel_mul i₁ i₃
      refine ⟨k, m, i₄, ?_⟩
      exact d.dec_aux h hm
    · obtain ⟨k, i₃, i₄, h⟩ := d.decY j i₂
      obtain ⟨m, hm⟩ := d.exists_Tel_mul i₁ i₃
      refine ⟨k, m, i₄, ?_⟩
      exact d.dec_aux h hm

theorem D_mem_of_le {H : Subgroup G} (hH : d.T ≤ H) {g : G} (hg : g ∈ H) :
    ∃ j i₁ i₂, g = d.Tel i₁ * d.D j * d.Tel i₂ ∧ d.D j ∈ H := by
  obtain ⟨j, i₁, i₂, rfl⟩ := d.cover g
  refine ⟨j, i₁, i₂, rfl, ?_⟩
  have h1 : d.Tel i₁ ∈ H := hH (d.Tel_mem_T i₁)
  have h2 : d.Tel i₂ ∈ H := hH (d.Tel_mem_T i₂)
  have : d.D j = (d.Tel i₁)⁻¹ * (d.Tel i₁ * d.D j * d.Tel i₂) * (d.Tel i₂)⁻¹ := by group
  rw [this]
  exact H.mul_mem (H.mul_mem (H.inv_mem h1) hg) (H.inv_mem h2)

theorem double_coset_mem {H : Subgroup G} (hH : d.T ≤ H) {j : κ} (hj : d.D j ∈ H) (i₁ i₂ : ι) :
    d.Tel i₁ * d.D j * d.Tel i₂ ∈ H :=
  H.mul_mem (H.mul_mem (hH (d.Tel_mem_T i₁)) hj) (hH (d.Tel_mem_T i₂))

theorem mem_A_iff (g : G) :
    g ∈ d.A ↔ ∃ j, (j = d.j0 ∨ j = d.ja) ∧ ∃ i₁ i₂, g = d.Tel i₁ * d.D j * d.Tel i₂ := by
  constructor
  · intro hg
    refine closure_subset_of_right_closed (S := {d.a, d.b, d.s, d.x})
      (P := {g | ∃ j, (j = d.j0 ∨ j = d.ja) ∧ ∃ i₁ i₂, g = d.Tel i₁ * d.D j * d.Tel i₂}) ?_ ?_ ?_ hg
    · rintro s (rfl | rfl | rfl | rfl)
      · exact ⟨4, by norm_num, d.ha⟩
      · exact ⟨4, by norm_num, d.hb⟩
      · exact ⟨2, by norm_num, d.hs⟩
      · exact ⟨3, by norm_num, d.hx⟩
    · exact ⟨d.j0, Or.inl rfl, d.i0, d.i0, by rw [d.Tel_zero, d.D_zero]; simp⟩
    · rintro _ ⟨j, hj, i₁, i₂, rfl⟩ s (rfl | rfl | rfl | rfl)
      · obtain ⟨k, hk⟩ := (d.Tel_next i₂).1
        exact ⟨j, hj, i₁, k, d.next_aux hk⟩
      · obtain ⟨k, hk⟩ := (d.Tel_next i₂).2.1
        exact ⟨j, hj, i₁, k, d.next_aux hk⟩
      · obtain ⟨k, hk⟩ := (d.Tel_next i₂).2.2
        exact ⟨j, hj, i₁, k, d.next_aux hk⟩
      · obtain ⟨k, hk, i₃, i₄, h⟩ := d.decXA j hj i₂
        obtain ⟨m, hm⟩ := d.exists_Tel_mul i₁ i₃
        refine ⟨k, hk, m, i₄, ?_⟩
        exact d.dec_aux h hm
  · rintro ⟨j, hj, i₁, i₂, rfl⟩
    refine d.A.mul_mem (d.A.mul_mem (d.T_le_A (d.Tel_mem_T i₁)) ?_) (d.T_le_A (d.Tel_mem_T i₂))
    rcases hj with rfl | rfl
    · rw [d.D_zero]; exact d.A.one_mem
    · exact d.D_ja

theorem mem_B_iff (g : G) :
    g ∈ d.B ↔ ∃ j, (j = d.j0 ∨ j = d.jb) ∧ ∃ i₁ i₂, g = d.Tel i₁ * d.D j * d.Tel i₂ := by
  constructor
  · intro hg
    refine closure_subset_of_right_closed (S := {d.a, d.b, d.s, d.y})
      (P := {g | ∃ j, (j = d.j0 ∨ j = d.jb) ∧ ∃ i₁ i₂, g = d.Tel i₁ * d.D j * d.Tel i₂}) ?_ ?_ ?_ hg
    · rintro s (rfl | rfl | rfl | rfl)
      · exact ⟨4, by norm_num, d.ha⟩
      · exact ⟨4, by norm_num, d.hb⟩
      · exact ⟨2, by norm_num, d.hs⟩
      · exact ⟨3, by norm_num, d.hy⟩
    · exact ⟨d.j0, Or.inl rfl, d.i0, d.i0, by rw [d.Tel_zero, d.D_zero]; simp⟩
    · rintro _ ⟨j, hj, i₁, i₂, rfl⟩ s (rfl | rfl | rfl | rfl)
      · obtain ⟨k, hk⟩ := (d.Tel_next i₂).1
        exact ⟨j, hj, i₁, k, d.next_aux hk⟩
      · obtain ⟨k, hk⟩ := (d.Tel_next i₂).2.1
        exact ⟨j, hj, i₁, k, d.next_aux hk⟩
      · obtain ⟨k, hk⟩ := (d.Tel_next i₂).2.2
        exact ⟨j, hj, i₁, k, d.next_aux hk⟩
      · obtain ⟨k, hk, i₃, i₄, h⟩ := d.decYB j hj i₂
        obtain ⟨m, hm⟩ := d.exists_Tel_mul i₁ i₃
        refine ⟨k, hk, m, i₄, ?_⟩
        exact d.dec_aux h hm
  · rintro ⟨j, hj, i₁, i₂, rfl⟩
    refine d.B.mul_mem (d.B.mul_mem (d.T_le_B (d.Tel_mem_T i₁)) ?_) (d.T_le_B (d.Tel_mem_T i₂))
    rcases hj with rfl | rfl
    · rw [d.D_zero]; exact d.B.one_mem
    · exact d.D_jb

theorem A_le_of_D_ja {H : Subgroup G} (hH : d.T ≤ H) (hj : d.D d.ja ∈ H) : d.A ≤ H := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl | rfl)
  · exact hH d.a_mem_T
  · exact hH d.b_mem_T
  · exact hH d.s_mem_T
  · exact (Subgroup.closure_le H).2 (by
      rintro g (rfl | rfl | rfl | rfl)
      · exact hH d.a_mem_T
      · exact hH d.b_mem_T
      · exact hH d.s_mem_T
      · exact hj) d.genA

theorem B_le_of_D_jb {H : Subgroup G} (hH : d.T ≤ H) (hj : d.D d.jb ∈ H) : d.B ≤ H := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl | rfl)
  · exact hH d.a_mem_T
  · exact hH d.b_mem_T
  · exact hH d.s_mem_T
  · exact (Subgroup.closure_le H).2 (by
      rintro g (rfl | rfl | rfl | rfl)
      · exact hH d.a_mem_T
      · exact hH d.b_mem_T
      · exact hH d.s_mem_T
      · exact hj) d.genB

theorem eq_top_of_xy {H : Subgroup G} (hH : d.T ≤ H) (hx : d.x ∈ H) (hy : d.y ∈ H) : H = ⊤ := by
  rw [eq_top_iff, ← d.gen]
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl | rfl | rfl)
  · exact hH d.a_mem_T
  · exact hH d.b_mem_T
  · exact hH d.s_mem_T
  · exact hx
  · exact hy

theorem eq_top_of_D {H : Subgroup G} (hH : d.T ≤ H) {j : κ} (h0 : j ≠ d.j0) (ha : j ≠ d.ja)
    (hb : j ≠ d.jb) (hj : d.D j ∈ H) : H = ⊤ := by
  obtain ⟨hx, hy⟩ := d.genO j h0 ha hb
  have hcl : Subgroup.closure ({d.a, d.b, d.s, d.D j} : Set G) ≤ H := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | rfl | rfl | rfl)
    · exact hH d.a_mem_T
    · exact hH d.b_mem_T
    · exact hH d.s_mem_T
    · exact hj
  exact d.eq_top_of_xy hH (hcl hx) (hcl hy)

theorem lattice (H : Subgroup G) (hH : d.T ≤ H) : H = d.T ∨ H = d.A ∨ H = d.B ∨ H = ⊤ := by
  by_cases hHT : H ≤ d.T
  · exact Or.inl (le_antisymm hHT hH)
  right
  obtain ⟨g, hgH, hgT⟩ : ∃ g ∈ H, g ∉ d.T := IsConcreteLE.not_le_iff_exists.1 hHT
  obtain ⟨j, i₁, i₂, hg, hjH⟩ := d.D_mem_of_le hH hgH
  have hj0 : j ≠ d.j0 := by
    rintro rfl
    apply hgT
    rw [hg, d.D_zero, mul_one]
    exact d.T.mul_mem (d.Tel_mem_T i₁) (d.Tel_mem_T i₂)
  have hfromA : d.A ≤ H → H = d.A ∨ H = d.B ∨ H = ⊤ := by
    intro hAH
    by_cases hHA : H ≤ d.A
    · exact Or.inl (le_antisymm hHA hAH)
    right
    obtain ⟨g', hg'H, hg'A⟩ : ∃ g ∈ H, g ∉ d.A := IsConcreteLE.not_le_iff_exists.1 hHA
    obtain ⟨j', k₁, k₂, hg', hj'H⟩ := d.D_mem_of_le hH hg'H
    have hj'0 : j' ≠ d.j0 ∧ j' ≠ d.ja := by
      constructor
      · rintro rfl
        exact hg'A ((d.mem_A_iff _).2 ⟨d.j0, Or.inl rfl, k₁, k₂, hg'⟩)
      · rintro rfl
        exact hg'A ((d.mem_A_iff _).2 ⟨d.ja, Or.inr rfl, k₁, k₂, hg'⟩)
    by_cases hjb : j' = d.jb
    · subst hjb
      exact Or.inr (d.eq_top_of_xy hH (hAH d.x_mem_A) (d.B_le_of_D_jb hH hj'H d.y_mem_B))
    · exact Or.inr (d.eq_top_of_D hH hj'0.1 hj'0.2 hjb hj'H)
  have hfromB : d.B ≤ H → H = d.B ∨ H = d.A ∨ H = ⊤ := by
    intro hBH
    by_cases hHB : H ≤ d.B
    · exact Or.inl (le_antisymm hHB hBH)
    right
    obtain ⟨g', hg'H, hg'B⟩ : ∃ g ∈ H, g ∉ d.B := IsConcreteLE.not_le_iff_exists.1 hHB
    obtain ⟨j', k₁, k₂, hg', hj'H⟩ := d.D_mem_of_le hH hg'H
    have hj'0 : j' ≠ d.j0 ∧ j' ≠ d.jb := by
      constructor
      · rintro rfl
        exact hg'B ((d.mem_B_iff _).2 ⟨d.j0, Or.inl rfl, k₁, k₂, hg'⟩)
      · rintro rfl
        exact hg'B ((d.mem_B_iff _).2 ⟨d.jb, Or.inr rfl, k₁, k₂, hg'⟩)
    by_cases hja : j' = d.ja
    · subst hja
      exact Or.inr (d.eq_top_of_xy hH (d.A_le_of_D_ja hH hj'H d.x_mem_A) (hBH d.y_mem_B))
    · exact Or.inr (d.eq_top_of_D hH hj'0.1 hja hj'0.2 hj'H)
  by_cases hja : j = d.ja
  · subst hja
    rcases hfromA (d.A_le_of_D_ja hH hjH) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  by_cases hjb : j = d.jb
  · subst hjb
    rcases hfromB (d.B_le_of_D_jb hH hjH) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  exact Or.inr (Or.inr (d.eq_top_of_D hH hj0 hja hjb hjH))

theorem D_ja_notMem_T : d.D d.ja ∉ d.T := fun h => by
  obtain ⟨i, hi⟩ := (d.mem_T_iff _).1 h
  exact d.sepA i hi

theorem D_jb_notMem_T : d.D d.jb ∉ d.T := fun h => by
  obtain ⟨i, hi⟩ := (d.mem_T_iff _).1 h
  exact d.sepB i hi

theorem T_ne_A : d.T ≠ d.A := fun h => d.D_ja_notMem_T (h ▸ d.D_ja)

theorem T_ne_B : d.T ≠ d.B := fun h => d.D_jb_notMem_T (h ▸ d.D_jb)

theorem inf_AB : d.A ⊓ d.B = d.T := by
  refine le_antisymm ?_ (le_inf d.T_le_A d.T_le_B)
  intro g ⟨hgA, hgB⟩
  obtain ⟨j, hj, i₁, i₂, hg⟩ := (d.mem_A_iff g).1 hgA
  obtain ⟨j', hj', k₁, k₂, hg'⟩ := (d.mem_B_iff g).1 hgB
  have hTT : ∀ m n : ι, d.Tel m * d.Tel n ∈ d.T := fun m n =>
    d.T.mul_mem (d.Tel_mem_T m) (d.Tel_mem_T n)
  rcases hj with rfl | rfl
  · rw [hg, d.D_zero, mul_one]
    exact hTT _ _
  rcases hj' with rfl | rfl
  · rw [hg', d.D_zero, mul_one]
    exact hTT _ _
  exfalso
  have h1 : d.D d.jb = (d.Tel k₁)⁻¹ * d.Tel i₁ * d.D d.ja * (d.Tel i₂ * (d.Tel k₂)⁻¹) := by
    have : d.Tel i₁ * d.D d.ja * d.Tel i₂ = d.Tel k₁ * d.D d.jb * d.Tel k₂ := hg.symm.trans hg'
    calc d.D d.jb = (d.Tel k₁)⁻¹ * (d.Tel k₁ * d.D d.jb * d.Tel k₂) * (d.Tel k₂)⁻¹ := by group
      _ = (d.Tel k₁)⁻¹ * (d.Tel i₁ * d.D d.ja * d.Tel i₂) * (d.Tel k₂)⁻¹ := by rw [this]
      _ = _ := by group
  obtain ⟨p, hp⟩ := (d.mem_T_iff ((d.Tel k₁)⁻¹ * d.Tel i₁)).1
    (d.T.mul_mem (d.T.inv_mem (d.Tel_mem_T k₁)) (d.Tel_mem_T i₁))
  obtain ⟨q, hq⟩ := (d.mem_T_iff (d.Tel i₂ * (d.Tel k₂)⁻¹)).1
    (d.T.mul_mem (d.Tel_mem_T i₂) (d.T.inv_mem (d.Tel_mem_T k₂)))
  exact d.sepAB p q (by rw [hp, hq]; exact h1.symm)

end OvergroupData

end CFSG.Quasithin
