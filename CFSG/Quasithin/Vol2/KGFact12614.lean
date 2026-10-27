module

public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

@[expose] def FactKv12614 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Y K T B : Subgroup Γ), K ≤ Y →
    Y ≤ Subgroup.normalizer (K : Set Γ) → IsSimpleGroup ↥K →
    CFSG.Milestones.SQTKSimpleList ↥K → CFSG.SectionRank.IsSQTKCat ↥K →
    IsSylowTwoOf T Y → Y = K ⊔ T → pCoreOf 2 Y = ⊥ → B < K →
    T ≤ Subgroup.normalizer (B : Set Γ) → ⁅B, B⁆ = B →
    quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)) →
    centralizerSection T B (pCoreOf 2 B) ≠ ⊥ →
      Nonempty (↥K ≃* ↥NativeSporadic.M22) ∨ Nonempty (↥K ≃* ↥NativeSporadic.M23)

@[expose] def FactM22M23NoFF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (W X K : Subgroup G) [IsMulCommutative ↥W],
    (∀ w ∈ W, w ^ 2 = 1) → X ≤ Subgroup.normalizer (W : Set G) → SQTKGroup ↥X →
    pCoreOf 2 (autOn X W) = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    (Nonempty (↥(autOn K W) ≃* ↥NativeSporadic.M22) ∨
      Nonempty (↥(autOn K W) ≃* ↥NativeSporadic.M23)) →
    (∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ K) → ¬ IsFFModule (V := ↥W) (autOn X W)

end CFSG.Quasithin.H13
