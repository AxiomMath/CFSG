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

namespace CFSG.Walter.J1Recog

variable {G : Type*} [Group G]

@[expose] def ee (t y : G) (i : ℕ) : G := (y ^ i)⁻¹ * t * y ^ i

theorem ee_zero (t y : G) : ee t y 0 = t := by simp [ee]

theorem ee_shift (t y : G) (i j : ℕ) : (y ^ j)⁻¹ * ee t y i * y ^ j = ee t y (i + j) := by
  simp only [ee, pow_add, mul_inv_rev, mul_assoc]

theorem ee_mul_shift {t y : G} {a b c : ℕ} (h : ee t y a * ee t y b = ee t y c) (j : ℕ) :
    ee t y (a + j) * ee t y (b + j) = ee t y (c + j) := by
  rw [← ee_shift, ← ee_shift, ← ee_shift, ← h]
  group

theorem ee_mod {t y : G} (hy : y ^ 7 = 1) (i : ℕ) : ee t y (i % 7) = ee t y i := by
  conv_rhs => rw [← Nat.mod_add_div i 7]
  simp only [ee, pow_add, pow_mul, hy, one_pow, mul_one]

theorem ee_mul_self {t y : G} (ht : t * t = 1) (i : ℕ) : ee t y i * ee t y i = 1 := by
  calc ee t y i * ee t y i = (y ^ i)⁻¹ * (t * t) * y ^ i := by simp only [ee]; group
    _ = 1 := by rw [ht, mul_one, inv_mul_cancel]

theorem ee_inv_eq (t y : G) (hy : y ^ 7 = 1) (i : ℕ) (hi : i ≤ 7) :
    y ^ i * t * (y ^ i)⁻¹ = ee t y (7 - i) := by
  have : y ^ (7 - i) = (y ^ i)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel hi, hy]
  rw [ee, this, inv_inv]

section Normal

structure IsCoord (S : Subgroup G) (t y : G) : Prop where
  card : Nat.card S = 8
  comm : ∀ x ∈ S, ∀ z ∈ S, x * z = z * x
  sq : ∀ x ∈ S, x * x = 1
  t_mem : t ∈ S
  t_ne : t ≠ 1
  y_mem : y ∈ Subgroup.normalizer (S : Set G)
  orderOf_y : orderOf y = 7
  free : ∀ x ∈ S, x ≠ 1 → y * x ≠ x * y

namespace IsCoord

variable {S : Subgroup G} {t y : G} (hc : IsCoord S t y)
include hc

theorem pow_seven : y ^ 7 = 1 := by rw [← hc.orderOf_y]; exact pow_orderOf_eq_one y

theorem ee_mem (i : ℕ) : ee t y i ∈ S := by
  have hyi : y ^ i ∈ Subgroup.normalizer (S : Set G) := Subgroup.pow_mem _ hc.y_mem i
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyi) t).mp hc.t_mem
  simpa [ee, mul_assoc] using this

theorem free_pow [Finite G] {j : ℕ} (hj0 : 0 < j) (hj7 : j < 7) {x : G} (hx : x ∈ S) (hx1 : x ≠ 1) :
    y ^ j * x ≠ x * y ^ j := by
  intro hcx
  apply hc.free x hx hx1
  have hord : orderOf (y ^ j) = 7 := by
    rw [orderOf_pow' y hj0.ne', hc.orderOf_y]
    have : Nat.gcd 7 j = 1 := by interval_cases j <;> norm_num
    rw [this, Nat.div_one]
  have hmemz : y ∈ Subgroup.zpowers (y ^ j) := by
    have hle : Subgroup.zpowers (y ^ j) ≤ Subgroup.zpowers y :=
      Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers y j)
    have heq : Subgroup.zpowers (y ^ j) = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hord, hc.orderOf_y])
    rw [heq]
    exact Subgroup.mem_zpowers y
  obtain ⟨k, hk⟩ := hmemz
  rw [← hk]
  exact (Commute.zpow_left hcx k)

theorem ee_ne [Finite G] {i j : ℕ} (hij : i < j) (hj : j < 7) : ee t y i ≠ ee t y j := by
  intro heq
  have h1 := congrArg (fun x => y ^ i * x * (y ^ i)⁻¹) heq
  have hji : ee t y j = (y ^ i)⁻¹ * ee t y (j - i) * y ^ i := by
    rw [ee_shift, Nat.sub_add_cancel hij.le]
  rw [hji] at h1
  simp only [ee, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at h1
  apply hc.free_pow (j := j - i) (by omega) (by omega) hc.t_mem hc.t_ne
  calc y ^ (j - i) * t = y ^ (j - i) * ((y ^ (j - i))⁻¹ * (t * y ^ (j - i))) := by
        rw [← h1]
    _ = t * y ^ (j - i) := by group

theorem ee_ne_one (i : ℕ) : ee t y i ≠ 1 := by
  intro h1
  apply hc.t_ne
  have := congrArg (fun x => y ^ i * x * (y ^ i)⁻¹) h1
  simpa [ee, mul_assoc] using this

theorem cover [Finite G] {x : G} (hx : x ∈ S) : x = 1 ∨ ∃ i < 7, x = ee t y i := by
  classical
  let f : Option (Fin 7) → S := fun o => match o with
    | none => 1
    | some i => ⟨ee t y i, hc.ee_mem i⟩
  have hf : Function.Injective f := by
    rintro (_ | i) (_ | j) hij
    · rfl
    · exact absurd (congrArg Subtype.val hij).symm (hc.ee_ne_one j)
    · exact absurd (congrArg Subtype.val hij) (hc.ee_ne_one i)
    · have h' : ee t y i = ee t y j := congrArg Subtype.val hij
      congr 1
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with hlt | hlt
      · exact hc.ee_ne hlt j.2 h'
      · exact hc.ee_ne hlt i.2 h'.symm
  have hbij : Function.Bijective f := by
    refine hf.bijective_of_nat_card_le ?_
    rw [hc.card, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]
  obtain ⟨o, ho⟩ := hbij.2 ⟨x, hx⟩
  rcases o with _ | i
  · left
    exact (congrArg Subtype.val ho).symm
  · right
    exact ⟨i, i.2, (congrArg Subtype.val ho).symm⟩

theorem inv : IsCoord S t y⁻¹ where
  card := hc.card
  comm := hc.comm
  sq := hc.sq
  t_mem := hc.t_mem
  t_ne := hc.t_ne
  y_mem := Subgroup.inv_mem _ hc.y_mem
  orderOf_y := by rw [orderOf_inv, hc.orderOf_y]
  free := fun x hx hx1 hcx => hc.free x hx hx1 (by
    calc y * x = y * (x * y⁻¹) * y := by group
      _ = y * (y⁻¹ * x) * y := by rw [hcx]
      _ = x * y := by group)

theorem exists_normal_form [Finite G] :
    ∃ z, (z = y ∨ z = y⁻¹) ∧ ee t z 0 * ee t z 2 = ee t z 3 := by
  have hy7 := hc.pow_seven
  have hmem := hc.ee_mem
  have hinj : ∀ i j : ℕ, i < j → j < 7 → ee t y i ≠ ee t y j := fun i j => hc.ee_ne
  have hne1 := hc.ee_ne_one
  have hcover : ∀ x ∈ S, x = 1 ∨ ∃ i < 7, x = ee t y i := fun x hx => hc.cover hx
  have hsq := hc.sq
  have hcomm := hc.comm
  have h01mem : ee t y 0 * ee t y 1 ∈ S := S.mul_mem (hmem 0) (hmem 1)
  have hsq' : ∀ i, ee t y i * ee t y i = 1 := fun i => hsq _ (hmem i)
  have hc : ∀ i j, ee t y i * ee t y j = ee t y j * ee t y i :=
    fun i j => hcomm _ (hmem i) _ (hmem j)
  rcases hcover _ h01mem with h01 | ⟨k, hk7, hk⟩
  · exfalso
    apply hinj 0 1 (by norm_num) (by norm_num)
    calc ee t y 0 = ee t y 0 * (ee t y 1 * ee t y 1) := by rw [hsq', mul_one]
      _ = ee t y 1 := by rw [← mul_assoc, h01, one_mul]
  have hsh : ∀ j, ee t y j * ee t y (1 + j) = ee t y (k + j) := by
    intro j
    have := ee_mul_shift hk j
    rwa [Nat.zero_add] at this
  have hmod : ∀ i, ee t y (i % 7) = ee t y i := ee_mod hy7
  have hcancL : ∀ a b c : ℕ, ee t y a * ee t y b = ee t y c → ee t y b = ee t y a * ee t y c := by
    intro a b c habc
    rw [← habc, ← mul_assoc, hsq', one_mul]
  interval_cases k
  ·
    exact absurd (mul_eq_left.mp hk) (hne1 1)
  · exact absurd (mul_eq_right.mp hk) (hne1 0)
  ·
    exfalso
    have h1 := hsh 1
    have h3 : ee t y 3 = ee t y 0 := by
      rw [show (2 + 1 : ℕ) = 3 from rfl] at h1
      rw [← h1, show (1 + 1 : ℕ) = 2 from rfl, ← hk, ← mul_assoc, hc 1 0, mul_assoc, hsq',
        mul_one]
    exact hinj 0 3 (by norm_num) (by norm_num) h3.symm
  ·
    refine ⟨y⁻¹, Or.inr rfl, ?_⟩
    have hz : ∀ i, i ≤ 7 → ee t y⁻¹ i = ee t y (7 - i) := by
      intro i hi
      rw [ee, inv_pow, inv_inv, ee_inv_eq t y hy7 i hi]
    rw [hz 0 (by norm_num), hz 2 (by norm_num), hz 3 (by norm_num)]
    have h4 := hsh 4
    rw [show (1 + 4 : ℕ) = 5 from rfl, show (3 + 4 : ℕ) = 7 from rfl, ← hmod 7,
      show 7 % 7 = 0 from rfl] at h4
    rw [show (7 - 0 : ℕ) = 7 from rfl, show (7 - 2 : ℕ) = 5 from rfl,
      show (7 - 3 : ℕ) = 4 from rfl, ← hmod 7, show 7 % 7 = 0 from rfl, ← h4, mul_assoc, hsq',
      mul_one]
  ·
    exfalso
    have h3 := hsh 3
    rw [show (1 + 3 : ℕ) = 4 from rfl, show (4 + 3 : ℕ) = 7 from rfl, ← hmod 7,
      show 7 % 7 = 0 from rfl] at h3
    have h4 : ee t y 4 = ee t y 3 * ee t y 0 := by
      rw [← h3, ← mul_assoc, hsq', one_mul]
    have : ee t y 1 = ee t y 3 := by
      have h' : ee t y 0 * ee t y 1 = ee t y 0 * ee t y 3 := by
        rw [hk, h4, hc 3 0]
      exact mul_left_cancel h'
    exact hinj 1 3 (by norm_num) (by norm_num) this
  ·
    refine ⟨y, Or.inl rfl, ?_⟩
    have h5 := hsh 5
    rw [show (1 + 5 : ℕ) = 6 from rfl, show (5 + 5 : ℕ) = 10 from rfl, ← hmod 10,
      show 10 % 7 = 3 from rfl] at h5
    have h1 := hsh 1
    rw [show (1 + 1 : ℕ) = 2 from rfl, show (5 + 1 : ℕ) = 6 from rfl] at h1
    rw [← h5, ← hk, ← h1, mul_assoc, ← mul_assoc (ee t y 1), hsq', one_mul]
  ·
    exfalso
    have h1 := hsh 1
    rw [show (1 + 1 : ℕ) = 2 from rfl, show (6 + 1 : ℕ) = 7 from rfl, ← hmod 7,
      show 7 % 7 = 0 from rfl] at h1
    have h2 : ee t y 2 = ee t y 1 * ee t y 0 := hcancL _ _ _ h1
    have : ee t y 2 = ee t y 6 := by rw [h2, hc 1 0, hk]
    exact hinj 2 6 (by norm_num) (by norm_num) this

end IsCoord

end Normal

end CFSG.Walter.J1Recog
