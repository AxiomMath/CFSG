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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.RankThree.PartOne.KCGeneric

variable {G : Type*} [Group G]

theorem eq_one_of_perfect_of_commutative {Q A : Type*} [Group Q] [Group A]
    (hP : Group.IsPerfect Q) (hA : ∀ a b : A, a * b = b * a) (φ : Q →* A) : ∀ g, φ g = 1 := by
  have hφ : (⊤ : Subgroup Q) ≤ φ.ker := by
    rw [← hP.commutator_eq_top]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hA (φ a) (φ b),
      mul_inv_cancel_right, mul_inv_cancel]
  intro g
  exact MonoidHom.mem_ker.mp (hφ (Subgroup.mem_top g))

theorem endo_eq_of_central_perfect {F Z : Subgroup G} (φ : G →* G) (hF : Group.IsPerfect F)
    (hZ : ∀ z ∈ Z, ∀ g : G, Commute z g) (h : ∀ g ∈ F, φ g * g⁻¹ ∈ Z) :
    ∀ g ∈ F, φ g = g := by
  let f : F →* Z :=
    { toFun := fun g => ⟨φ (g : G) * (g : G)⁻¹, h g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change φ ((a : G) * (b : G)) * ((a : G) * (b : G))⁻¹ =
          (φ (a : G) * (a : G)⁻¹) * (φ (b : G) * (b : G)⁻¹)
        have h1 : φ ((a : G) * (b : G)) * ((a : G) * (b : G))⁻¹ =
            φ (a : G) * (φ (b : G) * (b : G)⁻¹) * (a : G)⁻¹ := by
          rw [map_mul]
          group
        have hc := (hZ _ (h b b.2) (φ (a : G))).eq
        have h2 : φ (a : G) * (φ (b : G) * (b : G)⁻¹) * (a : G)⁻¹ =
            (φ (b : G) * (b : G)⁻¹) * (φ (a : G) * (a : G)⁻¹) := by
          calc φ (a : G) * (φ (b : G) * (b : G)⁻¹) * (a : G)⁻¹
              = ((φ (b : G) * (b : G)⁻¹) * φ (a : G)) * (a : G)⁻¹ := by rw [hc]
            _ = (φ (b : G) * (b : G)⁻¹) * (φ (a : G) * (a : G)⁻¹) := by group
        have h3 := (hZ _ (h a a.2) (φ (b : G) * (b : G)⁻¹)).eq
        rw [h1, h2, ← h3]) }
  have hφ := eq_one_of_perfect_of_commutative hF
    (fun a b : Z => Subtype.ext (hZ _ a.2 (b : G)).eq) f
  intro g hg
  have := congrArg Subtype.val (hφ ⟨g, hg⟩)
  exact mul_inv_eq_one.mp this

theorem fixed_of_commutes_of_perfect {U Γ : Type*} [Group U] [Group Γ] (ρ : U →* Γ)
    (hker : ∀ z ∈ ρ.ker, ∀ g : U, Commute z g) (c : U →* U) (ψ : Γ)
    (hψ : ∀ g, ψ * ρ g * ψ⁻¹ = ρ (c g)) {F : Subgroup U} (hF : Group.IsPerfect F)
    (hcomm : ∀ g ∈ F, ψ * ρ g = ρ g * ψ) : ∀ g ∈ F, c g = g := by
  refine endo_eq_of_central_perfect (Z := ρ.ker) c hF hker fun g hg => ?_
  rw [MonoidHom.mem_ker, map_mul, map_inv, ← hψ, hcomm g hg, mul_inv_cancel_right, mul_inv_cancel]

end CFSG.RankThree.PartOne.KCGeneric
