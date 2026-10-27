module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.D2Params

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.Open
open scoped Matrix

structure Core {U : Type} [CommGroup U] [Finite U] (X L₁ L₂ : Subgroup (MulAut U))
    (s : MulAut U) : Prop where
  exp : ∀ u : U, u ^ 2 = 1
  nt : Nontrivial U
  a38 : A38Types ↥L₁
  simple : IsSimpleGroup ↥L₁
  sqtk : SQTKGroup ↥L₁
  comm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x
  inf : L₁ ⊓ L₂ = ⊥
  le₁ : L₁ ≤ X
  le₂ : L₂ ≤ X
  mem : s ∈ X
  swap₁ : L₁.map (MulAut.conj s).toMonoidHom = L₂
  swap₂ : L₂.map (MulAut.conj s).toMonoidHom = L₁
  perm : ∀ x ∈ X, (L₁.map (MulAut.conj x).toMonoidHom = L₁ ∧
      L₂.map (MulAut.conj x).toMonoidHom = L₂) ∨
    (L₁.map (MulAut.conj x).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj x).toMonoidHom = L₁)
  two : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂
  o2 : pCoreOf 2 X = ⊥
  irr : ∀ J : Subgroup U, (∀ g ∈ L₁ ⊔ L₂, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤
  qhat : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ)

structure MatModel {U : Type} [CommGroup U] (L₁ L₂ : Subgroup (MulAut U)) (F : Type)
    [Field F] (d : ℕ) where
  β : U ≃* Multiplicative (Matrix (Fin d) (Fin d) F)
  R₁ : ↥L₁ →* Matrix.GeneralLinearGroup (Fin d) F
  R₂ : ↥L₂ →* Matrix.GeneralLinearGroup (Fin d) F
  act₁ : ∀ (l : ↥L₁) (u : U), β ((l : MulAut U) u) = Multiplicative.ofAdd
    (((R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
      Multiplicative.toAdd (β u))
  act₂ : ∀ (k : ↥L₂) (u : U), β ((k : MulAut U) u) = Multiplicative.ofAdd
    (Multiplicative.toAdd (β u) *
      ((R₂ k : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ)
  inj₁ : Function.Injective R₁
  span₁ : Submodule.span F (Set.range fun l : ↥L₁ =>
    ((R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)) = ⊤
  span₂ : Submodule.span F (Set.range fun k : ↥L₂ =>
    ((R₂ k : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)) = ⊤
  inj₂ : Function.Injective R₂
  irr₁ : ∀ S : AddSubgroup (Fin d → F), (∀ l : ↥L₁, ∀ v ∈ S,
    ((R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ S) →
      S = ⊥ ∨ S = ⊤
  end₁ : ∀ φ : (Fin d → F) →+ (Fin d → F), (∀ (l : ↥L₁) v,
    φ (((R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v) =
      ((R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ φ v) →
    ∃ c : F, ∀ v, φ v = c • v
  irr₂ : ∀ S : AddSubgroup (Fin d → F), (∀ k : ↥L₂, ∀ v ∈ S,
    ((R₂ k : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ S) →
      S = ⊥ ∨ S = ⊤
  end₂ : ∀ φ : (Fin d → F) →+ (Fin d → F), (∀ (k : ↥L₂) v,
    φ (((R₂ k : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v) =
      ((R₂ k : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ φ v) →
    ∃ c : F, ∀ v, φ v = c • v

end CFSG.Quasithin.SmithD37
