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

namespace CFSG.Quasithin

namespace G6

abbrev PermMod (n : ℕ) : Type := Multiplicative (Fin n → ZMod 2)

@[expose] def permAct (n : ℕ) : Equiv.Perm (Fin n) →* MulAut (PermMod n) where
  toFun σ :=
    { toFun := fun x => Multiplicative.ofAdd (fun i => Multiplicative.toAdd x (σ⁻¹ i))
      invFun := fun x => Multiplicative.ofAdd (fun i => Multiplicative.toAdd x (σ i))
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_mul' := fun x y => by
        apply Multiplicative.toAdd.injective
        funext i
        simp }
  map_one' := by
    ext x i
    simp
  map_mul' := fun σ τ => by
    ext x i
    simp [mul_inv_rev]

theorem permAct_apply (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : PermMod n) (i : Fin n) :
    Multiplicative.toAdd (permAct n σ x) i = Multiplicative.toAdd x (σ⁻¹ i) := rfl

@[expose] def coreMod (n : ℕ) : Subgroup (PermMod n) where
  carrier := {x | ∑ i, Multiplicative.toAdd x i = 0}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, toAdd_mul, Pi.add_apply, Finset.sum_add_distrib] at hx hy ⊢
    rw [hx, hy, add_zero]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    simp [hx]

theorem mem_coreMod {n : ℕ} {x : PermMod n} :
    x ∈ coreMod n ↔ ∑ i, Multiplicative.toAdd x i = 0 := Iff.rfl

theorem permAct_mem_coreMod {n : ℕ} (σ : Equiv.Perm (Fin n)) {x : PermMod n}
    (hx : x ∈ coreMod n) : permAct n σ x ∈ coreMod n := by
  rw [mem_coreMod] at hx ⊢
  simp only [permAct_apply]
  rw [← hx]
  exact Equiv.sum_comp σ⁻¹ (fun i => Multiplicative.toAdd x i)

@[expose] def coreAct (n : ℕ) : Equiv.Perm (Fin n) →* MulAut (coreMod n) where
  toFun σ :=
    { toFun := fun x => ⟨permAct n σ x, permAct_mem_coreMod σ x.2⟩
      invFun := fun x => ⟨permAct n σ⁻¹ x, permAct_mem_coreMod σ⁻¹ x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show permAct n σ⁻¹ (permAct n σ (x : PermMod n)) = x
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := fun x => by
        apply Subtype.ext
        show permAct n σ (permAct n σ⁻¹ (x : PermMod n)) = x
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      map_mul' := fun x y => by
        apply Subtype.ext
        simp }
  map_one' := by
    ext x
    simp
  map_mul' := fun σ τ => by
    ext x
    simp

theorem coreAct_coe (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : coreMod n) :
    ((coreAct n σ x : coreMod n) : PermMod n) = permAct n σ x := rfl

@[expose] def allOnes (n : ℕ) : PermMod n := Multiplicative.ofAdd (fun _ => (1 : ZMod 2))

@[expose] def natKer (n : ℕ) : Subgroup (coreMod n) :=
  (Subgroup.zpowers (allOnes n)).comap (coreMod n).subtype

variable {V : Type*} [CommGroup V]

@[expose] def IsSymModule (X : Subgroup (MulAut V)) (W : Subgroup V) (n : ℕ)
    (Z : Subgroup (coreMod n)) : Prop :=
  ∃ (θ : X ≃* Equiv.Perm (Fin n)) (β : coreMod n →* V),
    (∀ (x : X) (u : coreMod n), β (coreAct n (θ x) u) = (x : MulAut V) (β u)) ∧
      β.range = W ∧ β.ker = Z

@[expose] def IsSymNatural (X : Subgroup (MulAut V)) (W : Subgroup V) (n : ℕ) : Prop :=
  IsSymModule X W n (natKer n)

@[expose] def IsSymCore (X : Subgroup (MulAut V)) (W : Subgroup V) (n : ℕ) : Prop :=
  IsSymModule X W n ⊥

@[expose] def IsLnNatural (X : Subgroup (MulAut V)) (W : Subgroup V) (n : ℕ) : Prop :=
  Nonempty (X ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) ∧ Nat.card W = 2 ^ n ∧
    ∀ x ∈ X, (∀ w ∈ W, x w = w) → x = 1

end G6

end CFSG.Quasithin
