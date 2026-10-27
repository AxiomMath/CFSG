module

public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

open scoped Matrix

structure IsMatModel {V : Type} [CommGroup V] (D X : Subgroup (MulAut V)) {F : Type} [Field F]
    {d r : ℕ} (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F))
    (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F)
    (σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F) : Prop where
  hρ : ∀ (g : ↥D) (v : V), β ((g : MulAut V) v) =
    Multiplicative.ofAdd (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
      Matrix (Fin d) (Fin d) F) * Multiplicative.toAdd (β v))
  hσ : ∀ (x : ↥X) (v : V), β ((x : MulAut V) v) =
    Multiplicative.ofAdd (Multiplicative.toAdd (β v) *
      (((σ x : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ)
  I_irr : ∀ W : AddSubgroup (Fin d → F),
    (∀ (g : ↥D), ∀ w ∈ W, ((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
      Matrix (Fin d) (Fin d) F).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤
  comm_F : ∀ φ : (Fin d → F) →+ (Fin d → F),
    (∀ (g : ↥D) (w : Fin d → F), φ (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
      Matrix (Fin d) (Fin d) F).mulVec w) =
        ((ρ g : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F).mulVec (φ w)) →
      ∃ c : F, ∀ w, φ w = c • w
  U_irr : ∀ W : Submodule F (Fin r → F),
    (∀ (x : ↥X), ∀ w ∈ W, ((σ x : Matrix.GeneralLinearGroup (Fin r) F) :
      Matrix (Fin r) (Fin r) F).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def HasMatModel {V : Type} [CommGroup V] (D X : Subgroup (MulAut V)) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (d r : ℕ)
    (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F))
    (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F)
    (σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F),
    0 < d ∧ 0 < r ∧ IsMatModel D X β ρ σ

end CFSG.Quasithin
