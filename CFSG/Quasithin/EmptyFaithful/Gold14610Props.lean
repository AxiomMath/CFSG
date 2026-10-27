module

public import CFSG.Quasithin.EmptyFaithful.Gold14610Defs
public import CFSG.Quasithin.EmptyFaithful.S153DC27

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

namespace Gold14610

@[expose] def F618Core (Y : Type) [Group Y] : Prop :=
  (∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧ F6.IsL2 p 1 Y) ∨
  (∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ e ≤ 2 ∧ (p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) ∧ F6.IsL2 p e Y) ∨
  F6.IsHatAlt 6 Y ∨ Nonempty (Y ≃* alternatingGroup (Fin 7)) ∨ F6.IsHatAlt 7 Y ∨
  (∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ F6.IsL2 p 2 Y) ∨
  (∃ p : ℕ, (p % 8 = 3 ∨ p % 8 = 5) ∧ F6.IsSLEps3 p Y) ∨ F6.IsM12 Y

@[expose] def CentralExt3 (Kstar Y : Type) [Group Kstar] [Group Y] : Prop :=
  ∃ (X : Subgroup Kstar) (_ : X.Normal), X ≤ Subgroup.center Kstar ∧ ¬ 2 ∣ Nat.card X ∧
    Nat.Coprime (Nat.card X) 3 ∧ Nonempty (Kstar ⧸ X ≃* Y)

@[expose] def Cat3Type (Kstar : Type) [Group Kstar] : Prop :=
  ∃ (Y : Type) (_ : Group Y),
    (∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧ F6.IsL2 p 1 Y) ∧ CentralExt3 Kstar Y

variable {G : Type} [Group G]

@[expose] def AllowedShape (I K : Subgroup G) : Prop :=
  IsPSL 3 2 1 (OTwoQuot K) ∨
    (IsBlock2 I K ∧ (IsHatA6Block K ∨ IsG2Block K ∨ IsAltBlockType K 6 ∨ IsAltBlockType K 7 ∨
      IsExcA7Block K))

structure LiftConcl (T M I K : Subgroup G) : Prop where
  comp : K ∈ cComp I
  le : K ≤ I
  normal : I ≤ Subgroup.normalizer (K : Set G)
  quasi : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)
  not_le : ¬ K ≤ M
  cat : ∃ (Y : Type) (_ : Group Y), F618Core Y ∧ CentralExt3 (↥K ⧸ CFSG.pCore 2 ↥K) Y
  index : I = K ⊔ (T ⊓ I) ∨ Cat3Type (↥K ⧸ CFSG.pCore 2 ↥K)

@[expose] def Gold14610NoCase12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ : Subgroup G),
    Facts14610 T M H u I I₂ → IsSylowTwoOf (T ⊓ I) I →
    yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) →
    F6.IsGoldschmidtTripleIn I (i1Of1469 T M I) I₂ →
    ¬ F6.IsF618CaseOne (imgMod3 I (i1Of1469 T M I)) (imgMod3 I I₂) ∧
    ¬ F6.IsF618CaseOne (imgMod3 I I₂) (imgMod3 I (i1Of1469 T M I)) ∧
    ¬ F6.IsF618CaseTwo (↥I ⧸ CFSG.pPrimeCore 3 ↥I)

@[expose] def Gold14610F618Struct : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (D₁ D₂ : Subgroup D), IsGoldschmidtAmalgam D₁ D₂ →
    F6.F618ConclusionCat D₁ D₂ → ¬ F6.IsF618CaseOne D₁ D₂ → ¬ F6.IsF618CaseOne D₂ D₁ →
    ¬ F6.IsF618CaseTwo D →
    ∃ Kb : Subgroup D, CFSG.IsComponent Kb ∧ Kb.Normal ∧ F618Core ↥Kb ∧
      (((⊤ : Subgroup D) = Kb ⊔ (D₁ ⊓ D₂) ∧ twoResidual D₁ ≤ Kb ∧ twoResidual D₂ ≤ Kb) ∨
       (∃ Zb : Subgroup D, Zb.Normal ∧ (⊤ : Subgroup D) = Kb ⊔ Zb ⊔ (D₁ ⊓ D₂) ∧
          ¬ twoResidual D₁ ≤ Zb ∧
          ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧ F6.IsL2 p 1 ↥Kb))

@[expose] def Gold14610Lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ : Subgroup G),
    Facts14610 T M H u I I₂ → IsSylowTwoOf (T ⊓ I) I →
    yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) →
    F6.IsGoldschmidtTripleIn I (i1Of1469 T M I) I₂ →
    F6.F618ConclusionCat (imgMod3 I (i1Of1469 T M I)) (imgMod3 I I₂) →
    ¬ F6.IsF618CaseOne (imgMod3 I (i1Of1469 T M I)) (imgMod3 I I₂) →
    ¬ F6.IsF618CaseOne (imgMod3 I I₂) (imgMod3 I (i1Of1469 T M I)) →
    ¬ F6.IsF618CaseTwo (↥I ⧸ CFSG.pPrimeCore 3 ↥I) →
    ∃ K : Subgroup G, LiftConcl T M I K

@[expose] def Gold14610Compare : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M K V : Subgroup G), C27Concl H R M K V →
    K ∈ cComp H → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → CharTwo K → K ≤ H →
    H ≤ Subgroup.normalizer (K : Set G) → R ≤ Subgroup.normalizer (K : Set G) →
    (∃ (Y : Type) (_ : Group Y), F618Core Y ∧ CentralExt3 (↥K ⧸ CFSG.pCore 2 ↥K) Y) →
    AllowedShape H K ∧ ¬ Cat3Type (↥K ⧸ CFSG.pCore 2 ↥K)

@[expose] def Gold14610BlockOrders : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G),
    (IsAltBlockType K 6 → Nat.card (wOf1469 K) = 2 ^ 4 ∨ Nat.card (wOf1469 K) = 2 ^ 5) ∧
    (IsAltBlockType K 7 → Nat.card (wOf1469 K) = 2 ^ 6) ∧
    (IsExcA7Block K → Nat.card (wOf1469 K) = 2 ^ 4)

end Gold14610

end CFSG.Quasithin
