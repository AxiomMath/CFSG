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
public import Mathlib.GroupTheory.Nilpotent
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

open scoped Matrix

namespace CFSG.ASVolI.ChH

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {n : ℕ}

theorem card_le_card_mul_card_of_stabilizer_embeds {E : Subgroup (GL (Fin n) (ZMod 2))}
    {v : Fin n → ZMod 2} (S T : Submodule (ZMod 2) (Fin n → ZMod 2))
    (f : GL (Fin n) (ZMod 2) → Fin n → ZMod 2)
    (hS : ∀ k ∈ E, (k : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v - v ∈ S)
    (hT : ∀ k ∈ E, (k : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v → f k ∈ T)
    (hf : ∀ k₁ ∈ E, ∀ k₂ ∈ E, (k₁ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v →
      (k₂ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v → f k₁ = f k₂ → k₁ = k₂) :
    Nat.card E ≤ Nat.card S * Nat.card T := by
  letI : MulAction E (Fin n → ZMod 2) :=
    { smul := fun k w => ((k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w
      one_smul := fun w => by
        show ((1 : E) : GL (Fin n) (ZMod 2)).val *ᵥ w = w
        rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
      mul_smul := fun k l w => by
        show ((k * l : E) : GL (Fin n) (ZMod 2)).val *ᵥ w =
          (k : GL (Fin n) (ZMod 2)).val *ᵥ ((l : GL (Fin n) (ZMod 2)).val *ᵥ w)
        rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec] }
  have hsmul : ∀ (k : E) (w : Fin n → ZMod 2),
      k • w = ((k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w := fun _ _ => rfl
  have h1 : Nat.card (MulAction.orbit E v) * Nat.card (MulAction.stabilizer E v) = Nat.card E := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup E v)
  have h2 : Nat.card (MulAction.orbit E v) ≤ Nat.card S := by
    refine Nat.card_le_card_of_injective
      (fun p => (⟨p.1 - v, ?_⟩ : S)) ?_
    · obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp p.2
      rw [← hk, hsmul]
      exact hS k k.2
    · intro p q hpq
      have := congrArg Subtype.val hpq
      exact Subtype.ext (sub_left_inj.mp this)
  have h3 : Nat.card (MulAction.stabilizer E v) ≤ Nat.card T := by
    refine Nat.card_le_card_of_injective
      (fun p => (⟨f p.1.1, hT p.1.1 p.1.2 ?_⟩ : T)) ?_
    · exact MulAction.mem_stabilizer_iff.mp p.2
    · intro p q hpq
      have hp : ((p.1.1 : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v :=
        MulAction.mem_stabilizer_iff.mp p.2
      have hq : ((q.1.1 : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v :=
        MulAction.mem_stabilizer_iff.mp q.2
      exact Subtype.ext (Subtype.ext (hf p.1.1 p.1.2 q.1.1 q.1.2 hp hq (congrArg Subtype.val hpq)))
  calc Nat.card E = Nat.card (MulAction.orbit E v) * Nat.card (MulAction.stabilizer E v) := h1.symm
    _ ≤ Nat.card S * Nat.card T := Nat.mul_le_mul h2 h3

end CFSG.ASVolI.ChH
