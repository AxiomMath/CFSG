module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts24

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecB

@[expose] def FactSp4R2Big : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag24 L V X T V₁ V₂ n → KindSp4 L V n → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    ∀ A : Subgroup G, A ≤ pCoreOf 2 (LOf L V₂ ⊔ T) → IsElemAbelian 2 A →
      n < E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) →
        ⁅V, A⁆ = V₂ ∧ V ⊓ Subgroup.centralizer (A : Set G) = V₂

section CommSpace

variable {W : Type*} [Group W]

@[expose] def commSpace (E : Subgroup (MulAut W)) : Subgroup W :=
  Subgroup.closure {w | ∃ e ∈ E, ∃ u : W, w = e u * u⁻¹}

end CommSpace

@[expose] def FactG2LongRoot : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ ⊥ π →
      ∀ E : Subgroup (MulAut W), IsElemAbelian 2 E → (∀ e ∈ E, ∀ h ∈ H, e * h * e⁻¹ ∈ H) →
        Nat.card (commSpace E) ≤ 2 ^ (2 * n) → Nat.card E ≤ 2 ^ n

end CFSG.Quasithin.Vol2.Ch11.SecE
