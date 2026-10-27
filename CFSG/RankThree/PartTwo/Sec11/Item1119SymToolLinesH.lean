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

theorem aux_LinesH_prod_form3 {G : Type*} [Group G] (a c d : G)
    (hac : a * c = c * a) (had : a * d = d * a) (hcd : c * d = d * c)
    (i j l i' j' l' : ℤ) :
    (a ^ i * c ^ j * d ^ l) * (a ^ i' * c ^ j' * d ^ l') =
      a ^ (i + i') * c ^ (j + j') * d ^ (l + l') := by
  have had' : Commute a d := had
  have hac' : Commute a c := hac
  have hcd' : Commute c d := hcd
  have h1 : Commute (d ^ l) (a ^ i') := had'.symm.zpow_zpow l i'
  have h2 : Commute (c ^ j) (a ^ i') := hac'.symm.zpow_zpow j i'
  have h3 : Commute (d ^ l) (c ^ j') := hcd'.symm.zpow_zpow l j'
  calc (a ^ i * c ^ j * d ^ l) * (a ^ i' * c ^ j' * d ^ l')
      = a ^ i * (c ^ j * (d ^ l * a ^ i')) * (c ^ j' * d ^ l') := by
        simp only [mul_assoc]
    _ = a ^ i * (c ^ j * (a ^ i' * d ^ l)) * (c ^ j' * d ^ l') := by
        rw [h1.eq]
    _ = a ^ i * ((c ^ j * a ^ i') * d ^ l) * (c ^ j' * d ^ l') := by
        simp only [mul_assoc]
    _ = a ^ i * ((a ^ i' * c ^ j) * d ^ l) * (c ^ j' * d ^ l') := by
        rw [h2.eq]
    _ = a ^ i * a ^ i' * c ^ j * (d ^ l * c ^ j') * d ^ l' := by
        simp only [mul_assoc]
    _ = a ^ i * a ^ i' * c ^ j * (c ^ j' * d ^ l) * d ^ l' := by
        rw [h3.eq]
    _ = a ^ (i + i') * c ^ (j + j') * d ^ (l + l') := by
        simp only [zpow_add, mul_assoc]

theorem aux_LinesH_prod_form2 {G : Type*} [Group G] (e d : G) (hed : e * d = d * e)
    (i j i' j' : ℤ) :
    (e ^ i * d ^ j) * (e ^ i' * d ^ j') = e ^ (i + i') * d ^ (j + j') := by
  have h1 : Commute (d ^ j) (e ^ i') := (show Commute e d from hed).symm.zpow_zpow j i'
  calc (e ^ i * d ^ j) * (e ^ i' * d ^ j')
      = e ^ i * (d ^ j * e ^ i') * d ^ j' := by
        simp only [mul_assoc]
    _ = e ^ i * (e ^ i' * d ^ j) * d ^ j' := by
        rw [h1.eq]
    _ = e ^ (i + i') * d ^ (j + j') := by
        simp only [zpow_add, mul_assoc]

theorem aux_LinesH_closure_form3 {G : Type*} [Group G] (a c d : G)
    (hac : a * c = c * a) (had : a * d = d * a) (hcd : c * d = d * c) :
    ∀ g ∈ Subgroup.closure ({c, a, d} : Set G), ∃ i j l : ℤ, g = a ^ i * c ^ j * d ^ l := by
  let S : Subgroup G :=
    { carrier := {g | ∃ i j l : ℤ, g = a ^ i * c ^ j * d ^ l}
      mul_mem' := by
        rintro _ _ ⟨i, j, l, rfl⟩ ⟨i', j', l', rfl⟩
        exact ⟨i + i', j + j', l + l', aux_LinesH_prod_form3 a c d hac had hcd i j l i' j' l'⟩
      one_mem' := ⟨0, 0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, l, rfl⟩
        refine ⟨-i, -j, -l, ?_⟩
        apply inv_eq_of_mul_eq_one_right
        rw [aux_LinesH_prod_form3 a c d hac had hcd i j l (-i) (-j) (-l)]
        simp }
  have hsub : ({c, a, d} : Set G) ⊆ (S : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h
    · rw [h]; exact ⟨0, 1, 0, by simp⟩
    · rw [h]; exact ⟨1, 0, 0, by simp⟩
    · rw [h]; exact ⟨0, 0, 1, by simp⟩
  have hle : Subgroup.closure ({c, a, d} : Set G) ≤ S := (Subgroup.closure_le S).2 hsub
  intro g hg
  obtain ⟨i, j, l, h⟩ := hle hg
  exact ⟨i, j, l, h⟩

theorem aux_LinesH_closure_form2 {G : Type*} [Group G] (e d : G) (hed : e * d = d * e) :
    ∀ g ∈ Subgroup.closure ({e, d} : Set G), ∃ i j : ℤ, g = e ^ i * d ^ j := by
  let S : Subgroup G :=
    { carrier := {g | ∃ i j : ℤ, g = e ^ i * d ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
        exact ⟨i + i', j + j', aux_LinesH_prod_form2 e d hed i j i' j'⟩
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨-i, -j, ?_⟩
        apply inv_eq_of_mul_eq_one_right
        rw [aux_LinesH_prod_form2 e d hed i j (-i) (-j)]
        simp }
  have hsub : ({e, d} : Set G) ⊆ (S : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · rw [h]; exact ⟨1, 0, by simp⟩
    · rw [h]; exact ⟨0, 1, by simp⟩
  have hle : Subgroup.closure ({e, d} : Set G) ≤ S := (Subgroup.closure_le S).2 hsub
  intro g hg
  obtain ⟨i, j, h⟩ := hle hg
  exact ⟨i, j, h⟩

theorem aux_LinesH_conj_fix {G : Type*} [Group G] {x g : G} (h : x * g = g * x) (n : ℤ) :
    x ^ n * g * (x ^ n)⁻¹ = g := by
  have hc : Commute (x ^ n) g := (show Commute x g from h).zpow_left n
  rw [hc.eq, mul_inv_cancel_right]

theorem aux_LinesH_conj_zpow {G : Type*} [Group G] (X g : G) (n : ℤ) :
    X * g ^ n * X⁻¹ = (X * g * X⁻¹) ^ n :=
  conj_zpow.symm

theorem aux_LinesH_conj_a_nat {G : Type*} [Group G] (x a d : G) (m : ℤ)
    (hxa : x * a * x⁻¹ = d ^ m * a) (hxd : x * d = d * x) (k : ℕ) :
    x ^ (k : ℤ) * a * (x ^ (k : ℤ))⁻¹ = d ^ ((k : ℤ) * m) * a := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hdm : x * d ^ m = d ^ m * x := ((show Commute x d from hxd).zpow_right m).eq
    have hfix : x ^ (k : ℤ) * d ^ m * (x ^ (k : ℤ))⁻¹ = d ^ m :=
      aux_LinesH_conj_fix hdm (k : ℤ)
    push_cast
    calc x ^ ((k : ℤ) + 1) * a * (x ^ ((k : ℤ) + 1))⁻¹
        = x ^ (k : ℤ) * (x * a * x⁻¹) * (x ^ (k : ℤ))⁻¹ := by
          rw [zpow_add_one]
          simp only [mul_assoc, mul_inv_rev]
      _ = x ^ (k : ℤ) * (d ^ m * a) * (x ^ (k : ℤ))⁻¹ := by
          rw [hxa]
      _ = (x ^ (k : ℤ) * d ^ m * (x ^ (k : ℤ))⁻¹) * (x ^ (k : ℤ) * a * (x ^ (k : ℤ))⁻¹) := by
          simp only [mul_assoc, inv_mul_cancel_left]
      _ = d ^ m * (d ^ ((k : ℤ) * m) * a) := by
          rw [hfix, ih]
      _ = d ^ (((k : ℤ) + 1) * m) * a := by
          rw [show ((k : ℤ) + 1) * m = m + (k : ℤ) * m by ring, zpow_add, mul_assoc]

theorem aux_LinesH_conj_e {G : Type*} [Group G] (x a c d : G) (m : ℤ) (i j l n : ℤ)
    (hxc : x * c = c * x) (hxd : x * d = d * x) (had : a * d = d * a)
    (hP : x ^ n * a * (x ^ n)⁻¹ = d ^ (n * m) * a) :
    x ^ n * (a ^ i * c ^ j * d ^ l) * (x ^ n)⁻¹ =
      d ^ ((n * m) * i) * (a ^ i * c ^ j * d ^ l) := by
  have hC : x ^ n * c * (x ^ n)⁻¹ = c := aux_LinesH_conj_fix hxc n
  have hD : x ^ n * d * (x ^ n)⁻¹ = d := aux_LinesH_conj_fix hxd n
  have hcomm : Commute (d ^ (n * m)) a := (show Commute a d from had).symm.zpow_left (n * m)
  calc x ^ n * (a ^ i * c ^ j * d ^ l) * (x ^ n)⁻¹
      = (x ^ n * a ^ i * (x ^ n)⁻¹) * (x ^ n * c ^ j * (x ^ n)⁻¹)
          * (x ^ n * d ^ l * (x ^ n)⁻¹) := by
        simp only [mul_assoc, inv_mul_cancel_left]
    _ = (d ^ (n * m) * a) ^ i * c ^ j * d ^ l := by
        rw [aux_LinesH_conj_zpow, aux_LinesH_conj_zpow, aux_LinesH_conj_zpow, hP, hC, hD]
    _ = (d ^ (n * m)) ^ i * a ^ i * c ^ j * d ^ l := by
        rw [hcomm.mul_zpow]
    _ = d ^ ((n * m) * i) * (a ^ i * c ^ j * d ^ l) := by
        rw [← zpow_mul]
        simp only [mul_assoc]

theorem aux_LinesH_exists_nat (t M : ℤ) (hM : ¬ (3 : ℤ) ∣ M) :
    ∃ k : ℕ, (k : ℤ) * M % 3 = t % 3 := by
  have h3 : M % 3 = 1 ∨ M % 3 = 2 := by omega
  have ht : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases h3 with h3 | h3 <;> rcases ht with ht | ht | ht
  · exact ⟨0, by push_cast; omega⟩
  · exact ⟨1, by push_cast; omega⟩
  · exact ⟨2, by push_cast; omega⟩
  · exact ⟨0, by push_cast; omega⟩
  · exact ⟨2, by push_cast; omega⟩
  · exact ⟨1, by push_cast; omega⟩

theorem aux_LinesH_zpow_three_dvd {G : Type*} [Group G] (e : G) (he3 : e ^ (3 : ℤ) = 1)
    (s : ℤ) (hs : (3 : ℤ) ∣ s) : e ^ s = 1 := by
  obtain ⟨r, rfl⟩ := hs
  rw [zpow_mul, he3, one_zpow]

theorem x_conj_to_d_pow {G : Type*} [Group G] (x a c d e : G) (m : ℤ)
    (hxa : x * a * x⁻¹ = d ^ m * a) (hm : ¬ (3 : ℤ) ∣ m)
    (hxc : x * c = c * x) (hxd : x * d = d * x)
    (hac : a * c = c * a) (had : a * d = d * a) (hcd : c * d = d * c)
    (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hindep : a ∉ Subgroup.closure ({c, d} : Set G))
    (he : e ∈ Subgroup.closure ({c, a, d} : Set G))
    (hec : e ∉ Subgroup.closure ({c, d} : Set G)) :
    ∀ t : ℤ, ∃ n : ℤ, x ^ n * e * (x ^ n)⁻¹ = d ^ t * e := by
  intro t
  obtain ⟨i, j, l, hel⟩ := aux_LinesH_closure_form3 a c d hac had hcd e he
  have ha3' : a ^ (3 : ℤ) = 1 := by simpa using ha3
  have hd3' : d ^ (3 : ℤ) = 1 := by simpa using hd3
  have hc_mem : c ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hd_mem : d ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hi : ¬ (3 : ℤ) ∣ i := by
    rintro ⟨r, hr⟩
    apply hec
    rw [hel, hr, zpow_mul, ha3', one_zpow, one_mul]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hc_mem j) (Subgroup.zpow_mem _ hd_mem l)
  have hMi : ¬ (3 : ℤ) ∣ m * i := fun h => (Int.prime_three.dvd_or_dvd h).elim hm hi
  obtain ⟨k, hk⟩ := aux_LinesH_exists_nat t (m * i) hMi
  have hP := aux_LinesH_conj_a_nat x a d m hxa hxd k
  have hdexp : d ^ ((k : ℤ) * m * i) = d ^ t := by
    rw [mul_assoc, zpow_eq_zpow_emod ((k : ℤ) * (m * i)) hd3', zpow_eq_zpow_emod t hd3', hk]
  refine ⟨(k : ℤ), ?_⟩
  rw [hel, aux_LinesH_conj_e x a c d m i j l (k : ℤ) hxc hxd had hP, hdexp]

theorem mem_line_cases {G : Type*} [Group G] {e d z : G} (hed : e * d = d * e)
    (he3 : e ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hz : z ∈ Subgroup.closure ({e, d} : Set G)) (hzd : z ∉ Subgroup.zpowers d) :
    ∃ j : ℤ, z = d ^ j * e ∨ z = (d ^ j * e)⁻¹ := by
  obtain ⟨i, j, hij⟩ := aux_LinesH_closure_form2 e d hed z hz
  have he3' : e ^ (3 : ℤ) = 1 := by simpa using he3
  have hcomm : Commute e (d ^ j) := (show Commute e d from hed).zpow_right j
  have hi3 : ¬ (3 : ℤ) ∣ i := by
    rintro ⟨r, hr⟩
    apply hzd
    rw [hij, hr, zpow_mul, he3', one_zpow, one_mul]
    exact Subgroup.zpow_mem_zpowers d j
  have hmod : i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hmod with h1 | h2
  · have hei : e ^ i = e := by
      have h := aux_LinesH_zpow_three_dvd e he3' (i - 1) (by omega)
      calc e ^ i = e ^ (i - 1 + 1) := by rw [sub_add_cancel]
        _ = e ^ (i - 1) * e := by rw [zpow_add_one]
        _ = e := by rw [h, one_mul]
    refine ⟨j, Or.inl ?_⟩
    rw [hij, hei]
    exact hcomm.eq
  · have hei : e ^ i = e⁻¹ := by
      have h := aux_LinesH_zpow_three_dvd e he3' (i + 1) (by omega)
      rw [zpow_add_one] at h
      exact eq_inv_of_mul_eq_one_left h
    refine ⟨-j, Or.inr ?_⟩
    rw [hij, hei, mul_inv_rev, ← zpow_neg, neg_neg]

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
