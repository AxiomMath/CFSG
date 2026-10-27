module

public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.Quasithin.Background.G9StmtsModels
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace SzG11S

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def G112Concl13S (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  G112Concl13 Γ ∧
    (∃ Z : Subgroup ↥Γ, Z.Normal ∧ Nat.card ↥Z = 3 ∧
      ∀ N : Subgroup ↥Γ, N.Normal → N ≠ ⊥ → Z ≤ N) ∧
    ∃ N : Subgroup ↥Γ, N.Normal ∧ N.index = 2 ∧
      IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22

@[expose] def G112Concl7S (Γ X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  G112Concl7 Γ X ∧
    IsNaturalMatrixModule ((genFittingFStar ↥Γ).map Γ.subtype)
      (CFSG.Assembly.LowTwoRank.StatedOmega
        (CFSG.Assembly.LowTwoRank.StatedQuadPlus 2 (GaloisField 2 2)))

@[expose] def G112Concl6U33S (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  G112Concl6U33 Γ ∧
    IsG2NaturalModule Γ ⁅CFSG.Open.quasithinG2 (GaloisField 2 1),
      CFSG.Open.quasithinG2 (GaloisField 2 1)⁆

@[expose] def G112ConclusionFixS (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  (G112Concl1 Γ ∨ G112Concl2 Γ ∨ G112Concl3 Γ ∨ G112Concl4 Γ ∨ G112Concl5 B Γ ∨ G112Concl6 Γ ∨
    G112Concl7S Γ X ∨ G112Concl8 B Γ X ∨ G112Concl9 Γ ∨ G112Concl10 Γ X ∨ G112Concl11 Γ ∨
    G112Concl12 Γ X ∨ G112Concl13S Γ) ∨ G112Concl8S8 B Γ X ∨ G112Concl6U33S Γ

@[expose] def TheoremG112FixS : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G111Hyp B Γ v₁ W X X₀ → IsQuotientOfSQTKTauCeti ↥Γ → G112ConclusionFixS B Γ X

end SzG11S

end G11

end CFSG.Quasithin
