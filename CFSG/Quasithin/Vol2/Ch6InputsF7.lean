module

public import CFSG.Quasithin.Background.F7
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3

@[expose] def IsCharTwoBigE22 {Γ : Type} [Group Γ] (H M K : Subgroup Γ) : Prop :=
  (∃ m : ℕ, 3 ≤ m ∧ (IsPSL 2 2 m ↥(E2.star M H K) ∨ IsSz m ↥(E2.star M H K))) ∨
    ∃ m : ℕ, 2 ≤ m ∧ (IsPSU 3 2 m ↥(E2.star M H K) ∨ IsPSL 3 2 m ↥(E2.star M H K) ∨
      E2.IsSp4Prime m ↥(E2.star M H K))

@[expose] def F713Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ G₁ G₂ T V : Subgroup G),
    AmalgamHypV G₀ G₁ G₂ T V → V ≠ ⊥ → CFSG.SectionRank.IsSQTKCat ↥G₂ →
    ∀ γ : CosetGeom G₀ G₁ G₂, CosetGeom.IsCriticalVertex G₀ G₁ G₂ V γ →
      3 ≤ CosetGeom.critDist G₀ G₁ G₂ V → Odd (CosetGeom.critDist G₀ G₁ G₂ V) →
      IsUniqueMaxOver G₂ T (G₂ ⊓ Subgroup.normalizer (V : Set G)) → E1.nParam G₂ = 1 →
      (∀ K ∈ cComp G₂, ¬ IsCharTwoBigE22 G₂ (G₂ ⊓ Subgroup.normalizer (V : Set G)) K) →
      ∀ A : Subgroup G, A ≤ CosetGeom.Vv V (CosetGeom.γ₁ G₀ G₁ G₂) →
        ¬ A ≤ CosetGeom.ballStab 1 γ →
        ∃ α ∈ CosetGeom.nbrs γ,
          (A ⊓ Subgroup.normalizer (CosetGeom.Vv V α : Set G)).relIndex A = 2 ∧
          ∃ h ∈ CosetGeom.stab γ, conjSubgroup A h ≤ CosetGeom.stab α ∧
            ¬ IsPGroup 2 ↥(A ⊔ conjSubgroup A h)

end CFSG.Quasithin.H13
