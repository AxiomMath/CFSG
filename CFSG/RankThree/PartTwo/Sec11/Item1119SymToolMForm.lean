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

theorem aux_MForm_int_induction (P : ℤ → Prop) (h1 : P 1)
    (hadd : ∀ a b : ℤ, P a → P b → P (a + b)) (hneg : ∀ a : ℤ, P a → P (-a)) :
    ∀ n : ℤ, P n := by
  have hm1 : P (-1) := hneg 1 h1
  have h0 : P 0 := by
    have h := hadd 1 (-1) h1 hm1
    simpa using h
  intro n
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i ih => exact hadd _ _ ih h1
  | pred i ih =>
    have h := hadd _ _ ih hm1
    rwa [← sub_eq_add_neg] at h

theorem mem_closure_normal_form {G : Type*} [Group G] (A : Subgroup G) (y r : G)
    (hAy : ∀ u ∈ A, u * y = y * u) (hAr : ∀ u ∈ A, u * r = r * u)
    (hk : y * r * y⁻¹ * r⁻¹ ∈ A) {m : G}
    (hm : m ∈ Subgroup.closure ((A : Set G) ∪ {y, r})) :
    ∃ (i j : ℤ) (u : G), u ∈ A ∧ m = y ^ i * r ^ j * u := by
  have hAy' : ∀ u ∈ A, ∀ n : ℤ, u * y ^ n = y ^ n * u := fun u hu n =>
    ((show Commute u y from hAy u hu).zpow_right n).eq
  have hAr' : ∀ u ∈ A, ∀ n : ℤ, u * r ^ n = r ^ n * u := fun u hu n =>
    ((show Commute u r from hAr u hu).zpow_right n).eq
  obtain ⟨k, hk_def⟩ : ∃ k : G, k = y * r * y⁻¹ * r⁻¹ := ⟨_, rfl⟩
  rw [← hk_def] at hk
  have hky : k * y = y * k := hAy k hk
  have hkr : k * r = r * k := hAr k hk
  have hrel : k * r * y = y * r := by
    rw [hk_def]
    group
  have hcr : k * (r * y) = r * y * k := by
    rw [← mul_assoc, hkr, mul_assoc, hky, ← mul_assoc]
  have hry1 : r * y = y * r * k⁻¹ := by
    rw [← hrel, mul_assoc k r y, hcr, mul_inv_cancel_right]
  have hB1 : ∀ j : ℤ, ∃ w ∈ A, r ^ j * y = y * r ^ j * w := by
    refine aux_MForm_int_induction (fun j : ℤ => ∃ w ∈ A, r ^ j * y = y * r ^ j * w) ?_ ?_ ?_
    · refine ⟨k⁻¹, A.inv_mem hk, ?_⟩
      rw [zpow_one]
      exact hry1
    · rintro a b ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
      refine ⟨w₁ * w₂, A.mul_mem hw₁ hw₂, ?_⟩
      calc r ^ (a + b) * y = r ^ a * (r ^ b * y) := by rw [zpow_add, mul_assoc]
        _ = r ^ a * (y * r ^ b * w₂) := by rw [h₂]
        _ = (r ^ a * y) * r ^ b * w₂ := by simp only [mul_assoc]
        _ = (y * r ^ a * w₁) * r ^ b * w₂ := by rw [h₁]
        _ = y * (r ^ a * (w₁ * r ^ b)) * w₂ := by simp only [mul_assoc]
        _ = y * (r ^ a * (r ^ b * w₁)) * w₂ := by rw [hAr' w₁ hw₁ b]
        _ = y * (r ^ a * r ^ b) * (w₁ * w₂) := by simp only [mul_assoc]
        _ = y * r ^ (a + b) * (w₁ * w₂) := by rw [zpow_add]
    · rintro a ⟨w, hw, h⟩
      refine ⟨w⁻¹, A.inv_mem hw, ?_⟩
      have hyr : y * r ^ a = r ^ a * y * w⁻¹ := by
        rw [h, mul_inv_cancel_right]
      have e1 : r ^ (-a) * y * r ^ a = y * w⁻¹ := by
        calc r ^ (-a) * y * r ^ a = r ^ (-a) * (y * r ^ a) := by rw [mul_assoc]
          _ = r ^ (-a) * (r ^ a * y * w⁻¹) := by rw [hyr]
          _ = y * w⁻¹ := by group
      have e2 : r ^ (-a) * y = y * w⁻¹ * r ^ (-a) := by
        calc r ^ (-a) * y = r ^ (-a) * y * r ^ a * r ^ (-a) := by group
          _ = y * w⁻¹ * r ^ (-a) := by rw [e1]
      calc r ^ (-a) * y = y * w⁻¹ * r ^ (-a) := e2
        _ = y * (w⁻¹ * r ^ (-a)) := by rw [mul_assoc]
        _ = y * (r ^ (-a) * w⁻¹) := by rw [hAr' w⁻¹ (A.inv_mem hw) (-a)]
        _ = y * r ^ (-a) * w⁻¹ := by rw [mul_assoc]
  have hKL : ∀ i j : ℤ, ∃ w ∈ A, r ^ j * y ^ i = y ^ i * r ^ j * w := by
    refine aux_MForm_int_induction
      (fun i : ℤ => ∀ j : ℤ, ∃ w ∈ A, r ^ j * y ^ i = y ^ i * r ^ j * w) ?_ ?_ ?_
    · intro j
      obtain ⟨w, hw, h⟩ := hB1 j
      refine ⟨w, hw, ?_⟩
      rw [zpow_one]
      exact h
    · intro a b Ha Hb j
      obtain ⟨w₁, hw₁, h₁⟩ := Ha j
      obtain ⟨w₂, hw₂, h₂⟩ := Hb j
      refine ⟨w₂ * w₁, A.mul_mem hw₂ hw₁, ?_⟩
      calc r ^ j * y ^ (a + b) = (r ^ j * y ^ a) * y ^ b := by rw [zpow_add, mul_assoc]
        _ = (y ^ a * r ^ j * w₁) * y ^ b := by rw [h₁]
        _ = y ^ a * (r ^ j * (w₁ * y ^ b)) := by simp only [mul_assoc]
        _ = y ^ a * (r ^ j * (y ^ b * w₁)) := by rw [hAy' w₁ hw₁ b]
        _ = (y ^ a * (r ^ j * y ^ b)) * w₁ := by simp only [mul_assoc]
        _ = (y ^ a * (y ^ b * r ^ j * w₂)) * w₁ := by rw [h₂]
        _ = y ^ (a + b) * r ^ j * (w₂ * w₁) := by rw [zpow_add]; simp only [mul_assoc]
    · intro a Ha j
      obtain ⟨w, hw, h⟩ := Ha j
      refine ⟨w⁻¹, A.inv_mem hw, ?_⟩
      have e1 : y ^ (-a) * r ^ j = r ^ j * y ^ (-a) * w := by
        calc y ^ (-a) * r ^ j = y ^ (-a) * (r ^ j * y ^ a) * y ^ (-a) := by group
          _ = y ^ (-a) * (y ^ a * r ^ j * w) * y ^ (-a) := by rw [h]
          _ = r ^ j * w * y ^ (-a) := by group
          _ = r ^ j * (w * y ^ (-a)) := by simp only [mul_assoc]
          _ = r ^ j * (y ^ (-a) * w) := by rw [hAy' w hw (-a)]
          _ = r ^ j * y ^ (-a) * w := by simp only [mul_assoc]
      calc r ^ j * y ^ (-a) = r ^ j * y ^ (-a) * w * w⁻¹ := by group
        _ = y ^ (-a) * r ^ j * w⁻¹ := by rw [← e1]
  let S : Subgroup G :=
    { carrier := {g | ∃ (i j : ℤ) (u : G), u ∈ A ∧ g = y ^ i * r ^ j * u}
      mul_mem' := by
        rintro g h ⟨i, j, u, hu, rfl⟩ ⟨i', j', u', hu', rfl⟩
        obtain ⟨w, hw, hrw⟩ := hKL i' j
        refine ⟨i + i', j + j', w * u * u', A.mul_mem (A.mul_mem hw hu) hu', ?_⟩
        calc y ^ i * r ^ j * u * (y ^ i' * r ^ j' * u')
            = y ^ i * r ^ j * (u * y ^ i') * r ^ j' * u' := by simp only [mul_assoc]
          _ = y ^ i * r ^ j * (y ^ i' * u) * r ^ j' * u' := by rw [hAy' u hu i']
          _ = y ^ i * (r ^ j * y ^ i') * (u * r ^ j') * u' := by simp only [mul_assoc]
          _ = y ^ i * (r ^ j * y ^ i') * (r ^ j' * u) * u' := by rw [hAr' u hu j']
          _ = y ^ i * (y ^ i' * r ^ j * w) * (r ^ j' * u) * u' := by rw [hrw]
          _ = y ^ i * y ^ i' * r ^ j * (w * r ^ j') * u * u' := by simp only [mul_assoc]
          _ = y ^ i * y ^ i' * r ^ j * (r ^ j' * w) * u * u' := by rw [hAr' w hw j']
          _ = y ^ (i + i') * r ^ (j + j') * (w * u * u') := by
              rw [zpow_add, zpow_add]; simp only [mul_assoc]
      one_mem' := ⟨0, 0, 1, A.one_mem, by simp⟩
      inv_mem' := by
        rintro g ⟨i, j, u, hu, rfl⟩
        obtain ⟨w, hw, hrw⟩ := hKL (-i) (-j)
        refine ⟨-i, -j, u⁻¹ * w, A.mul_mem (A.inv_mem hu) hw, ?_⟩
        calc (y ^ i * r ^ j * u)⁻¹ = u⁻¹ * (r ^ (-j) * y ^ (-i)) := by group
          _ = u⁻¹ * (y ^ (-i) * r ^ (-j) * w) := by rw [hrw]
          _ = u⁻¹ * y ^ (-i) * r ^ (-j) * w := by simp only [mul_assoc]
          _ = y ^ (-i) * u⁻¹ * r ^ (-j) * w := by rw [hAy' u⁻¹ (A.inv_mem hu) (-i)]
          _ = y ^ (-i) * (u⁻¹ * r ^ (-j)) * w := by simp only [mul_assoc]
          _ = y ^ (-i) * (r ^ (-j) * u⁻¹) * w := by rw [hAr' u⁻¹ (A.inv_mem hu) (-j)]
          _ = y ^ (-i) * r ^ (-j) * (u⁻¹ * w) := by simp only [mul_assoc] }
  have hS : ∀ g : G, g ∈ S ↔ ∃ (i j : ℤ) (u : G), u ∈ A ∧ g = y ^ i * r ^ j * u :=
    fun g => Iff.rfl
  have hAS : ∀ u ∈ A, u ∈ S := fun u hu => (hS u).mpr ⟨0, 0, u, hu, by simp⟩
  have hyS : y ∈ S := (hS y).mpr ⟨1, 0, 1, A.one_mem, by simp⟩
  have hrS : r ∈ S := (hS r).mpr ⟨0, 1, 1, A.one_mem, by simp⟩
  have hsub : ((A : Set G) ∪ {y, r}) ⊆ (S : Set G) := by
    intro x hx
    rcases (Set.mem_union x _ _).mp hx with hxA | hxyr
    · exact hAS x hxA
    · rcases Set.mem_insert_iff.mp hxyr with h | h
      · rw [h]
        exact hyS
      · rw [Set.mem_singleton_iff.mp h]
        exact hrS
  have hle : Subgroup.closure ((A : Set G) ∪ {y, r}) ≤ S := (Subgroup.closure_le S).mpr hsub
  obtain ⟨i, j, u, hu, hmeq⟩ := (hS m).mp (hle hm)
  exact ⟨i, j, u, hu, hmeq⟩

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
