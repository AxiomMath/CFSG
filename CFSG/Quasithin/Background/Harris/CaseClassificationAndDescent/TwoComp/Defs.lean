module

public import CFSG.Quasithin.Background.Harris.Interfaces

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
  CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure Setting (Γ A L L₂ : Subgroup (GLV V)) (m : ℕ) : Prop where
  hyp : G93Hyp Γ A L (L ⊔ L₂) m
  comp₂ : IsComponentOf L₂ Γ
  ne : L₂ ≠ L
  qe : QuasiEquivalent L L₂

theorem Setting.of_data {Γ A L H L₂ : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L H m)
    (hc : IsComponentOf L₂ Γ) (hne : L₂ ≠ L) (hH : H = L ⊔ L₂) (hq : QuasiEquivalent L L₂) :
    Setting Γ A L L₂ m := by
  subst hH
  exact ⟨h, hc, hne, hq⟩

@[expose] def IsTensorModel (d : ℕ) (K : Type) [Field K] [Algebra (ZMod 2) K]
    (H : Subgroup (GLV V)) : Prop :=
  ∃ (φ : ↥H ≃* (↥(StatedSL d K) × ↥(StatedSL d K)))
    (ψ : V ≃ₗ[ZMod 2] Matrix (Fin d) (Fin d) K), ∀ (γ : ↥H) (v : V),
      ψ ((γ : GLV V) v) =
        (((φ γ).1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) * ψ v *
          (((φ γ).2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
