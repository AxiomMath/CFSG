module

public import CFSG.Milestones.ASVolI.G11

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin.HatM22 CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def G112Concl13ModN (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 12 ∧
    ∃ N : Subgroup ↥Γ, N.Normal ∧ N.index = 2 ∧ IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22 ∧
      ∃ ψ : V ≃ₗ[ZMod 2] (Fin 6 → FieldFour), ∀ k ∈ N.map Γ.subtype, ∃ γ : ↥hatM22Γ₀, ∀ v : V,
        ψ (k v) = (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour)).mulVec (ψ v)

end CFSG.Quasithin.G112A2

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped TensorProduct

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def G112FaithfulM (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)) : Prop :=
  (Module.finrank (ZMod 2) V = 2 ∧ Nonempty (↥Γ ≃* Equiv.Perm (Fin 3))) ∨
  (Module.finrank (ZMod 2) V = 4 ∧ (10 ∣ Nat.card ↥Γ ∨ 18 ∣ Nat.card ↥Γ)) ∨
  (Module.finrank (ZMod 2) V = 6 ∧ IsSubSD16Heis Γ) ∨
  G112Concl4 Γ ∨
  G112Concl5 B Γ ∨
  (Module.finrank (ZMod 2) V = 6 ∧ IsG2NaturalModule Γ (CFSG.Open.quasithinG2 (ZMod 2))) ∨
  (Module.finrank (ZMod 2) V = 8 ∧
    IsNaturalMatrixModule (fStarIn Γ) (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) ∧
    ¬ X ≤ fStarIn Γ) ∨
  G112Concl8 B Γ X ∨ G112Concl8S8 B Γ X ∨
  IsG112Nine Γ ∨
  IsG112Ten Γ X ∨
  (Module.finrank (ZMod 2) V = 8 ∧ IsL28TwistedTensorModule (fStarIn Γ)) ∨
  G112Concl12 Γ X ∨
  CFSG.Quasithin.G112A2.G112Concl13ModN Γ

@[expose] def G112FaithfulWithU33M (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ X : Subgroup (GLV V)) : Prop :=
  G112FaithfulM B Γ X ∨ G112ProposedU33 Γ

section CounterexampleM

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure G11CanonicalCxM (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)) : Prop where
  hyp : G111Hyp B Γ v₁ W X X₀
  sqtk : IsQuotientOfSQTKTauCeti ↥Γ
  notConcl : ¬ G112FaithfulWithU33M B Γ X

structure G11CanonicalSetupM (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) : Prop where
  cx : G11CanonicalCxM B Γ v₁ W X X₀
  h108 : G108Hyp B Γ v₁ W X X₀ L
  numConj : numConjugates Γ L ≤ 2

end CounterexampleM

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG

@[expose] def G_11_2M : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G111Hyp B Γ v₁ W X X₀ → IsQuotientOfSQTKTauCeti ↥Γ → G112FaithfulWithU33M B Γ X

end CFSG.ASVolI

namespace CFSG.Quasithin.G11

namespace Canon

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Quasithin.G11.G117 CFSG.Quasithin.G11.SzG11S

structure QContainsM (Q : ConclPred) : Prop where
  c2 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 4 ∧ (10 ∣ Nat.card ↥Γ ∨ 18 ∣ Nat.card ↥Γ)) → Q B Γ X
  c4 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)), G112Concl4 Γ → Q B Γ X
  c5 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)), G112Concl5 B Γ → Q B Γ X
  c6 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 6 ∧ IsG2NaturalModule Γ (CFSG.Open.quasithinG2 (ZMod 2))) →
      Q B Γ X
  c6' : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 6 ∧
      IsG2NaturalModule Γ ⁅CFSG.Open.quasithinG2 (ZMod 2), CFSG.Open.quasithinG2 (ZMod 2)⁆) →
      Q B Γ X
  c7 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 8 ∧
      IsNaturalMatrixModule ((genFittingFStar ↥Γ).map Γ.subtype)
        (CFSG.Assembly.LowTwoRank.StatedOmega
          (CFSG.Assembly.LowTwoRank.StatedQuadPlus 2 (GaloisField 2 2))) ∧
      ¬ X ≤ (genFittingFStar ↥Γ).map Γ.subtype) → Q B Γ X
  c10 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)), IsG112Ten Γ X → Q B Γ X
  c11 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 8 ∧
      IsL28TwistedTensorModule ((genFittingFStar ↥Γ).map Γ.subtype)) → Q B Γ X
  c13 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 12 ∧ ∃ N : Subgroup ↥Γ, N.Normal ∧ N.index = 2 ∧
      IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22 ∧ IsIrr (N.map Γ.subtype) ⊤) → Q B Γ X

end Canon

end CFSG.Quasithin.G11
