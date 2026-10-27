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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

variable {p : ℕ} [Fact p.Prime]

abbrev VM (p : ℕ) : Type := Multiplicative (Fin 5 → ZMod p)

instance : Finite (VM p) := inferInstanceAs (Finite (Fin 5 → ZMod p))

theorem card_comap_eq {G G' : Type*} [Group G] [Group G'] [Finite G] (φ : G →* G')
    (A : Subgroup G') (hA : A ≤ φ.range) : Nat.card (A.comap φ) = Nat.card A * Nat.card φ.ker := by
  have h1 := Subgroup.relIndex_mul_card (H := φ.ker) (K := A.comap φ)
  rw [Subgroup.relIndex_ker, Subgroup.map_comap_eq, inf_eq_right.2 hA,
    inf_eq_left.2 (fun x hx => by
      have : φ x = 1 := hx
      simp [this, A.one_mem] : φ.ker ≤ A.comap φ)] at h1
  rw [← h1, mul_comm]

@[expose] def constSub (p : ℕ) [Fact p.Prime] : Subgroup (VM p) where
  carrier := {a | ∀ s t, Multiplicative.toAdd a s = Multiplicative.toAdd a t}
  mul_mem' := by
    intro a b ha hb s t
    simp only [toAdd_mul, Pi.add_apply]
    rw [ha s t, hb s t]
  one_mem' := by intro s t; rfl
  inv_mem' := by
    intro a ha s t
    simp only [toAdd_inv, Pi.neg_apply]
    rw [ha s t]

theorem card_constSub : Nat.card (constSub p) = p := by
  have e : constSub p ≃ ZMod p :=
    { toFun := fun a => Multiplicative.toAdd (a : VM p) 0
      invFun := fun c => ⟨Multiplicative.ofAdd (fun _ => c), fun _ _ => rfl⟩
      left_inv := fun a => by
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        funext s
        exact (a.2 s 0).symm ▸ rfl
      right_inv := fun c => rfl }
  rw [Nat.card_congr e, Nat.card_zmod]

@[expose] def diffHom (k l : Fin 5) : VM p →* Multiplicative (ZMod p) where
  toFun a := Multiplicative.ofAdd (Multiplicative.toAdd a k - Multiplicative.toAdd a l)
  map_one' := by simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, Pi.add_apply]
    ring

@[expose] def Hsub (p : ℕ) [Fact p.Prime] (k l : Fin 5) : Subgroup (VM p) := (diffHom k l).ker

theorem mem_Hsub {k l : Fin 5} {a : VM p} :
    a ∈ Hsub p k l ↔ Multiplicative.toAdd a k = Multiplicative.toAdd a l := by
  unfold Hsub
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd (Multiplicative.toAdd a k - Multiplicative.toAdd a l) = 1 ↔ _
  rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, sub_eq_zero]

theorem card_le_mul_inf_Hsub (k l : Fin 5) (A : Subgroup (VM p)) :
    Nat.card A ≤ p * Nat.card (Hsub p k l ⊓ A : Subgroup (VM p)) := by
  have h1 := Subgroup.relIndex_mul_card (H := Hsub p k l) (K := A)
  have h2 : (Hsub p k l).relIndex A ≤ p := by
    unfold Hsub
    rw [Subgroup.relIndex_ker]
    calc Nat.card (A.map (diffHom k l)) ≤ Nat.card (Multiplicative (ZMod p)) :=
          Subgroup.card_le_card_group _
      _ = p := by simp
  rw [← h1]
  exact Nat.mul_le_mul_right _ h2

theorem card_le_pow_three (S : Set (VM p)) (i j k l m : Fin 5)
    (hcov : ∀ t, t = i ∨ t = j ∨ t = k ∨ t = l ∨ t = m)
    (hS : ∀ a ∈ S, Multiplicative.toAdd a i = Multiplicative.toAdd a j ∧
      Multiplicative.toAdd a k = Multiplicative.toAdd a l) : Nat.card S ≤ p ^ 3 := by
  have hinj : Function.Injective (fun a : S =>
      ((Multiplicative.toAdd a.1 i, Multiplicative.toAdd a.1 k, Multiplicative.toAdd a.1 m) :
        ZMod p × ZMod p × ZMod p)) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2, h4⟩ := hab
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext t
    rcases hcov t with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · rw [← (hS a ha).1, ← (hS b hb).1]; exact h1
    · exact h2
    · rw [← (hS a ha).2, ← (hS b hb).2]; exact h2
    · exact h4
  calc Nat.card S ≤ Nat.card (ZMod p × ZMod p × ZMod p) :=
        Nat.card_le_card_of_injective _ hinj
    _ = p ^ 3 := by simp; ring

theorem card_le_pow_three' (S : Set (VM p)) (i₀ i i' j j' : Fin 5)
    (hcov : ∀ t, t = i₀ ∨ t = i ∨ t = i' ∨ t = j ∨ t = j')
    (hS : ∀ a ∈ S, Multiplicative.toAdd a i' = 2 * Multiplicative.toAdd a i₀ -
        Multiplicative.toAdd a i ∧
      Multiplicative.toAdd a j' = 2 * Multiplicative.toAdd a i₀ - Multiplicative.toAdd a j) :
    Nat.card S ≤ p ^ 3 := by
  have hinj : Function.Injective (fun a : S =>
      ((Multiplicative.toAdd a.1 i₀, Multiplicative.toAdd a.1 i, Multiplicative.toAdd a.1 j) :
        ZMod p × ZMod p × ZMod p)) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2, h3⟩ := hab
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext t
    rcases hcov t with h | h | h | h | h
    · rw [h]; exact h1
    · rw [h]; exact h2
    · rw [h, (hS a ha).1, (hS b hb).1, h1, h2]
    · rw [h]; exact h3
    · rw [h, (hS a ha).2, (hS b hb).2, h1, h3]
  calc Nat.card S ≤ Nat.card (ZMod p × ZMod p × ZMod p) :=
        Nat.card_le_card_of_injective _ hinj
    _ = p ^ 3 := by simp; ring

end CFSG.RankThree.PartOne.U5K.Kf
