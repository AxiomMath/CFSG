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
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

namespace A318P

open Matrix


variable {K : Type} [Field K]

@[expose] def heisA (ω : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, ω, ω ^ 2]

@[expose] def heisB : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem det_heisA {ω : K} (hω : ω ^ 3 = 1) : (heisA ω).det = 1 := by
  simp [heisA, det_diagonal, Fin.prod_univ_three]
  linear_combination hω

theorem det_heisB : (heisB : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [heisB, det_fin_three]

theorem heisA_pow_three {ω : K} (hω : ω ^ 3 = 1) : heisA ω ^ 3 = 1 := by
  rw [heisA, diagonal_pow, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp
  · linear_combination hω
  · linear_combination (ω ^ 3 + 1) * hω

theorem heisB_pow_three : (heisB : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisB, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem heisA_mul_heisB {ω : K} (hω : ω ^ 3 = 1) :
    heisA ω * heisB = ω • (heisB * heisA ω) := by
  ext i j
  rw [heisA, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [heisB]
  all_goals first | ring1 | linear_combination hω | linear_combination (-1 : K) * hω



theorem heis_indep {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (i j : ℕ) (c : K)
    (h : heisA ω ^ i * (heisB : Matrix (Fin 3) (Fin 3) K) ^ j = Matrix.scalar (Fin 3) c) :
    3 ∣ i ∧ 3 ∣ j := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hA3 : heisA ω ^ 3 = 1 := heisA_pow_three hω
  have hB3 : (heisB : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := heisB_pow_three
  have hi : heisA ω ^ i = heisA ω ^ (i % 3) := by
    conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, hA3, one_pow, mul_one]
  have hj : (heisB : Matrix (Fin 3) (Fin 3) K) ^ j = heisB ^ (j % 3) := by
    conv_lhs => rw [← Nat.mod_add_div j 3, pow_add, pow_mul, hB3, one_pow, mul_one]
  rw [hi, hj] at h
  have hi3 : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hj3 : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    apply hω1
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hω, h2]; simp
  have key : i % 3 = 0 ∧ j % 3 = 0 := by
    have e0 := congr_fun (congr_fun h 0) 0
    have e1 := congr_fun (congr_fun h 1) 1
    have e10 := congr_fun (congr_fun h 1) 0
    have e20 := congr_fun (congr_fun h 2) 0
    interval_cases hj' : j % 3 <;> interval_cases hi' : i % 3 <;>
      simp [heisA, heisB, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
        Matrix.diagonal_apply] at e0 e1 e10 e20 ⊢
    all_goals first
      | exact hω0 e10
      | exact hω0 e20
      | exact hω1 (e1.trans e0.symm)
      | exact hω2 (by rw [pow_two]; exact e1.trans e0.symm)
  omega


@[expose] def c3Hom {Q : Type*} [Group Q] (g : Q) (hg : g ^ 3 = 1) : Multiplicative (ZMod 3) →* Q where
  toFun x := g ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    have hpow : ∀ n : ℕ, g ^ n = g ^ (n % 3) := by
      intro n
      conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hg, one_pow, mul_one]
    simp only [toAdd_mul, ZMod.val_add]
    rw [← hpow, pow_add]

theorem c3Hom_apply {Q : Type*} [Group Q] (g : Q) (hg : g ^ 3 = 1) (x : Multiplicative (ZMod 3)) :
    c3Hom g hg x = g ^ (Multiplicative.toAdd x).val := rfl

theorem exists_nine_of_commuting {Q : Type*} [Group Q] {u v : Q} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (hcomm : u * v = v * u) (hind : ∀ i j : ℕ, u ^ i * v ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) :
    ∃ E : Subgroup Q, Nat.card E = 9 ∧ (∀ a b : E, a * b = b * a) ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ∀ f : Q →* Q, f u = u → f v = v → ∀ y ∈ E, f y = y := by
  let F : Multiplicative (ZMod 3) × Multiplicative (ZMod 3) →* Q :=
    (c3Hom u hu).noncommCoprod (c3Hom v hv) (fun a b => by
      simp only [c3Hom_apply]
      exact (Commute.pow_pow hcomm _ _))
  have hF : ∀ a b : Multiplicative (ZMod 3), F (a, b) = u ^ (Multiplicative.toAdd a).val *
      v ^ (Multiplicative.toAdd b).val := fun a b => by
    simp [F, MonoidHom.noncommCoprod_apply, c3Hom_apply]
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    rw [hF] at h
    obtain ⟨h1, h2⟩ := hind _ _ h
    have ha : Multiplicative.toAdd a = 0 := by
      have := ZMod.val_lt (Multiplicative.toAdd a)
      have h0 : (Multiplicative.toAdd a).val = 0 := by omega
      exact (ZMod.val_eq_zero _).1 h0
    have hb : Multiplicative.toAdd b = 0 := by
      have := ZMod.val_lt (Multiplicative.toAdd b)
      have h0 : (Multiplicative.toAdd b).val = 0 := by omega
      exact (ZMod.val_eq_zero _).1 h0
    exact Prod.ext (Multiplicative.toAdd.injective (by simpa using ha))
      (Multiplicative.toAdd.injective (by simpa using hb))
  refine ⟨F.range, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hFinj).toEquiv, Nat.card_prod]
    simp
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    change F a * F b = F b * F a
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have hx : ∀ x : Multiplicative (ZMod 3), x ^ 3 = 1 := fun x => by
      have := pow_card_eq_one' (G := Multiplicative (ZMod 3)) (x := x)
      simpa using this
    have : a ^ 3 = 1 := Prod.ext (hx a.1) (hx a.2)
    rw [this, map_one]
  · rintro f hfu hfv _ ⟨⟨a, b⟩, rfl⟩
    rw [hF, map_mul, map_pow, map_pow, hfu, hfv]


end A318P

end CFSG.Quasithin
