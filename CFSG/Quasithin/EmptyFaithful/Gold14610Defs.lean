module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

namespace Gold14610

variable {G : Type} [Group G]

@[expose] def oPrime3 (I : Subgroup G) : Subgroup G := (CFSG.pPrimeCore 3 ↥I).map I.subtype

@[expose] def imgMod3 (I X : Subgroup G) : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I) :=
  (X.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))

structure Concl14610CoreW (I K : Subgroup G) : Prop where
  shape : IsPSL 3 2 1 (OTwoQuot K) ∨
    (IsBlock2 I K ∧
      (IsHatA6Block K ∨ IsG2Block K ∨
       (IsAlt 6 (OTwoQuot K) ∧
         (Nat.card (wOf1469 K) = 2 ^ 4 ∨ Nat.card (wOf1469 K) = 2 ^ 5)) ∨
       (IsAlt 7 (OTwoQuot K) ∧
         (Nat.card (wOf1469 K) = 2 ^ 4 ∨ Nat.card (wOf1469 K) = 2 ^ 6))))

@[expose] def Input14610ListW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ : Subgroup G),
    ASC27Statement G → Facts14610 T M H u I I₂ → IsSylowTwoOf (T ⊓ I) I →
    yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) →
    F6.IsGoldschmidtTripleIn I (i1Of1469 T M I) I₂ →
    F6.F618ConclusionCat (imgMod3 I (i1Of1469 T M I)) (imgMod3 I I₂) →
    Concl14610CoreW I (oTwoUpper I)

end Gold14610

end CFSG.Quasithin
