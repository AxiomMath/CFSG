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

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral

variable {Γ : Type*} [Group Γ]

theorem exists_diagonalHom [Finite Γ] {a : Γ} (V : Subgroup Γ)
    (hcomm : ∀ g h : Subgroup.zpowers a, g ≠ h → ∀ x ∈ V, ∀ y ∈ V,
      Commute ((g : Γ) * x * (g : Γ)⁻¹) ((h : Γ) * y * (h : Γ)⁻¹)) :
    ∃ δ : V →* Γ, (∀ w : V, a * δ w * a⁻¹ = δ w) ∧
      (∀ H : Subgroup Γ, (∀ g ∈ Subgroup.zpowers a, ∀ x ∈ V, g * x * g⁻¹ ∈ H) →
        ∀ w : V, δ w ∈ H) ∧
      (∀ w : V, a * w * a⁻¹ = w → δ w = (w : Γ) ^ Nat.card (Subgroup.zpowers a)) := by
  classical
  have : Fintype (Subgroup.zpowers a) := Fintype.ofFinite _
  let φ : ∀ _ : Subgroup.zpowers a, V →* Γ := fun g =>
    (MulAut.conj (g : Γ)).toMonoidHom.comp V.subtype
  have hφ : ∀ g x, φ g x = (g : Γ) * x * (g : Γ)⁻¹ := fun g x => rfl
  have hcomm' : Pairwise fun g h : Subgroup.zpowers a => ∀ x y : V, Commute (φ g x) (φ h y) :=
    fun g h hgh x y => hcomm g h hgh x x.2 y y.2
  let Δ : ((_ : Subgroup.zpowers a) → V) →* Γ := MonoidHom.noncommPiCoprod φ hcomm'
  let diag : V →* ((_ : Subgroup.zpowers a) → V) := MonoidHom.pi fun _ => MonoidHom.id V
  refine ⟨Δ.comp diag, fun w => ?_, fun H hH w => ?_, fun w hw => ?_⟩
  · let ga : Subgroup.zpowers a := ⟨a, Subgroup.mem_zpowers a⟩
    let shift : ((_ : Subgroup.zpowers a) → V) →* ((_ : Subgroup.zpowers a) → V) :=
      { toFun := fun f g => f (ga⁻¹ * g)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have key : (MulAut.conj a).toMonoidHom.comp Δ = Δ.comp shift := by
      refine MonoidHom.pi_ext fun g x => ?_
      have hs : shift (Pi.mulSingle g x) = Pi.mulSingle (ga * g) x := by
        funext h
        simp only [shift, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mulSingle_apply,
          inv_mul_eq_iff_eq_mul]
      change a * Δ (Pi.mulSingle g x) * a⁻¹ = Δ (shift (Pi.mulSingle g x))
      rw [hs, MonoidHom.noncommPiCoprod_mulSingle, MonoidHom.noncommPiCoprod_mulSingle, hφ, hφ]
      simp only [Subgroup.coe_mul, ga, mul_inv_rev]
      group
    have h1 := congrArg (fun f : _ →* Γ => f (diag w)) key
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have h2 : shift (diag w) = diag w := rfl
    rw [h2] at h1
    exact h1
  · change Δ (diag w) ∈ H
    rw [MonoidHom.noncommPiCoprod_apply]
    exact Subgroup.noncommProd_mem H _ fun g _ => hH g g.2 w w.2
  · have hfix : ∀ g ∈ Subgroup.zpowers a, g * (w : Γ) * g⁻¹ = w := by
      intro g hg
      have hle : Subgroup.zpowers a ≤ Subgroup.centralizer ({(w : Γ)} : Set Γ) :=
        Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hw))
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp (hle hg))
    change Δ (diag w) = _
    rw [MonoidHom.noncommPiCoprod_apply, Finset.noncommProd_eq_pow_card _ _ _ (w : Γ)
      fun g _ => (hφ g (diag w g)).trans (hfix g g.2)]
    simp [Finset.card_univ, Nat.card_eq_fintype_card]

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral
