module

public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def ExcNoSuzukiReeAt (C : Type) [Group C] (I : Subgroup (MulAut C)) : Prop :=
  ∀ (p : ℕ) (β : MulAut C), p.Prime → p ≠ 2 → β ≠ 1 → β ^ p = 1 → β ∈ I →
    ∀ X : Subgroup C,
      IsComponentOf X (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup β) →
        LargeEvenMarking ↥X (fun _ _ _ _ _ _ => True) →
          LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GGChevStTag lab)

@[expose] def ExcNoSuzukiReeE6
    : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
    ExcNoSuzukiReeAt ↥(adjointGroup .E6 K)
      ((MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range ⊔
        (AutSt.e6DiagHom K).range)

@[expose] def ExcNoSuzukiReeTwE6
    : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ f) →
      ExcNoSuzukiReeAt ↥(twistedE6RootGroup K σ) (twistedE6Inn K σ ⊔ twistedE6Diag K σ)

end CFSG.StandardType
