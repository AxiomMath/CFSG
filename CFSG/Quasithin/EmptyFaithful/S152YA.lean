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

namespace CFSG.Quasithin.S152Y

open Matrix

abbrev Vec3 : Type := Fin 3 → ZMod 2

abbrev SL3 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

@[expose] def mulV (g : SL3) (v : Vec3) : Vec3 := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v

@[expose] def plane (f : Vec3) : Finset Vec3 := Finset.univ.filter (fun v => f ⬝ᵥ v = 0)

@[expose] def Planes : Finset (Finset Vec3) :=
  (Finset.univ.filter (fun f : Vec3 => f ≠ 0)).image plane

theorem mulV_mul (g h : SL3) (v : Vec3) : mulV (g * h) v = mulV g (mulV h v) := by
  simp [mulV, Matrix.mulVec_mulVec]

theorem mulV_one (v : Vec3) : mulV 1 v = v := by simp [mulV]

theorem mulV_add (g : SL3) (u v : Vec3) : mulV g (u + v) = mulV g u + mulV g v := by
  simp [mulV, Matrix.mulVec_add]

theorem mulV_zero (g : SL3) : mulV g 0 = 0 := by simp [mulV]

theorem mulV_inj (g : SL3) : Function.Injective (mulV g) := by
  intro u v h
  have := congrArg (mulV g⁻¹) h
  simpa [← mulV_mul, mulV_one] using this

set_option maxRecDepth 100000

theorem planes_card_four : ∀ A ∈ Planes, A.card = 4 := by decide +kernel

theorem mem_planes_of : ∀ A ∈ (Finset.univ : Finset (Finset Vec3)), A.card = 4 → (0 : Vec3) ∈ A →
    (∀ a ∈ A, ∀ b ∈ A, a + b ∈ A) → A ∈ Planes := by
  decide +kernel

theorem planes_image : ∀ A ∈ Planes, ∀ g ∈ (Finset.univ : Finset SL3), A.image (mulV g) ∈ Planes := by
  decide +kernel

theorem planes_trans : ∀ A ∈ Planes, ∀ B ∈ Planes, ∃ g : SL3, A.image (mulV g) = B := by decide +kernel

theorem planes_two_trans : ∀ B₁ ∈ Planes, ∀ B₂ ∈ Planes, ∀ C₁ ∈ Planes, ∀ C₂ ∈ Planes, B₁ ≠ B₂ → C₁ ≠ C₂ →
    ∃ g : SL3, B₁.image (mulV g) = C₁ ∧ B₂.image (mulV g) = C₂ := by decide +kernel

theorem three_planes : ∀ p : Vec3, p ≠ 0 → ∃ B₁ ∈ Planes, ∃ B₂ ∈ Planes, ∃ B₃ ∈ Planes,
    B₁ ≠ B₂ ∧ B₁ ≠ B₃ ∧ B₂ ≠ B₃ ∧ p ∈ B₁ ∧ p ∈ B₂ ∧ p ∈ B₃ := by decide +kernel

theorem planes_meet : ∀ B ∈ Planes, ∀ C ∈ Planes, B ≠ C → ∃ p : Vec3, p ≠ 0 ∧ B ∩ C = {0, p} := by
  decide +kernel

theorem two_in_plane : ∀ p ∈ (Finset.univ : Finset Vec3), ∀ q ∈ (Finset.univ : Finset Vec3), p ≠ 0 → q ≠ 0 →
    p ≠ q → ∃ B ∈ Planes, p ∈ B ∧ q ∈ B := by decide +kernel

theorem card_stab : ∀ A ∈ Planes,
    (Finset.univ.filter (fun g : SL3 => A.image (mulV g) = A)).card = 24 := by
  decide +kernel

theorem fix_lemma : ∀ A ∈ Planes, ∀ a ∈ A, a ≠ 0 → ∀ b : Vec3,
    (∀ g : SL3, A.image (mulV g) = A → mulV g a = a → mulV g b = b) → b = 0 ∨ b = a := by
  decide +kernel

theorem cube_one : ∀ A ∈ Planes, ∀ g ∈ (Finset.univ : Finset SL3), A.image (mulV g) = A →
    (∀ a ∈ A, a ≠ 0 → mulV g a ≠ a) → g ^ 3 = 1 := by decide +kernel

@[expose] def stabSub (A : Finset Vec3) : Subgroup SL3 where
  carrier := {g | A.image (mulV g) = A}
  one_mem' := by
    show A.image (mulV 1) = A
    have : mulV 1 = id := funext mulV_one
    rw [this]
    simp
  mul_mem' := by
    intro g h hg hh
    have hg' : A.image (mulV g) = A := hg
    have hh' : A.image (mulV h) = A := hh
    show A.image (mulV (g * h)) = A
    have : mulV (g * h) = mulV g ∘ mulV h := funext fun v => mulV_mul g h v
    rw [this, ← Finset.image_image, hh', hg']
  inv_mem' := by
    intro g hg
    have hg' : A.image (mulV g) = A := hg
    show A.image (mulV g⁻¹) = A
    have h1 : mulV g⁻¹ ∘ mulV g = id := funext fun v => by
      simp [← mulV_mul, mulV_one]
    calc A.image (mulV g⁻¹) = (A.image (mulV g)).image (mulV g⁻¹) := by rw [hg']
      _ = A.image (mulV g⁻¹ ∘ mulV g) := Finset.image_image
      _ = A := by rw [h1]; simp

theorem natCard_stabSub {A : Finset Vec3} (hA : A ∈ Planes) : Nat.card (stabSub A) = 24 := by
  classical
  have h := card_stab A hA
  rw [Nat.card_eq_fintype_card]
  rw [← h]
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.refl _)

theorem image_eq_of_subset {A : Finset Vec3} {g : SL3} (h : ∀ a ∈ A, mulV g a ∈ A) :
    A.image (mulV g) = A := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact h a ha
  · rw [Finset.card_image_of_injective _ (mulV_inj g)]

end CFSG.Quasithin.S152Y
