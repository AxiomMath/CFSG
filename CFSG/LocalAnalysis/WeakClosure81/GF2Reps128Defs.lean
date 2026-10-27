module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped Matrix

@[expose] def W4Lem6_3Swap : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (L : Subgroup (MulAut W)) (t : MulAut W), CFSG.Open.IsQuasisimple ↥L → orderOf t = 2 →
      L.map (MulAut.conj t).toMonoidHom ≠ L → ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥ →
      IsIrrOn (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥ →
      (∀ x ∈ L, ∀ w ∈ commV (Subgroup.zpowers t), (x * (t * x * t⁻¹)) w = w) →
      dMinDeg ↥L ≤ rkIdx (fixV (Subgroup.zpowers t)) ∨
        ∃ e : ℕ, IsNaturalO4Plus (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) e ∧
          rkIdx (fixV (Subgroup.zpowers t)) = e ∧ dMinDeg ↥L = 2 * e ∧
          ∀ s : MulAut W, s * s = 1 →
            L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom →
            rkIdx (fixV (Subgroup.zpowers s)) = e →
            s ∈ L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t

variable {W : Type} [CommGroup W]

@[expose] def IsMatTensor2 (L L' : Subgroup (MulAut W)) (K : Type) [Field K] : Prop :=
  ∃ (φ₁ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K) (φ₂ : ↥L' ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (ψ : W ≃* Multiplicative (Matrix (Fin 2) (Fin 2) K)),
    (∀ (x : ↥L) (w : W), Multiplicative.toAdd (ψ ((x : MulAut W) w)) =
      ((φ₁ x : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        Multiplicative.toAdd (ψ w)) ∧
    (∀ (y : ↥L') (w : W), Multiplicative.toAdd (ψ ((y : MulAut W) w)) =
      Multiplicative.toAdd (ψ w) *
        ((φ₂ y : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ)

end CFSG.LocalAnalysis.WeakClosure81
