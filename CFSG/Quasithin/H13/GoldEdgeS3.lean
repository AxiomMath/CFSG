module

public import CFSG.Quasithin.Recognition.GoldschmidtTriple

public section

namespace CFSG.Quasithin.H13

@[expose] def GoldschmidtEdgeBoundS3 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtAmalgam G₁ G₂ →
    Nat.card ↥(G₁ ⊓ G₂) ≤ 2 ^ 7

theorem card_inf_le_of_goldschmidtEdgeBoundS3 (hb : GoldschmidtEdgeBoundS3) {D : Type} [Group D]
    [Finite D] {G₁ G₂ : Subgroup D} (h : IsGoldschmidtAmalgam G₁ G₂) :
    Nat.card ↥(G₁ ⊓ G₂) ≤ 2 ^ 7 :=
  hb D G₁ G₂ h

end CFSG.Quasithin.H13
