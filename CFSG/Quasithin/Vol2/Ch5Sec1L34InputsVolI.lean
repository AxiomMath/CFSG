module

public import CFSG.Quasithin.Background.F918C3
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def AS_I_E_5_4 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (X P : Subgroup Γ) (j : ℕ), 0 < j → IsSylowTwoOf P X →
    CharTwo X → CFSG.IsQuasisimple ↥(CFSG.Open.quasithinGenFitting (⊤ : Subgroup (O2Q X))) →
    CFSG.Open.pRank 2 (⊤ : Subgroup (O2Q X)) ≤ j →
    (∀ Y : Subgroup Γ, (Y.subgroupOf X).Normal → pCoreOf 2 X ≤ Y → Y ≤ solvRad X →
      HasNoFaithfulFFModulesMod X Y) →
      X ≤ Subgroup.normalizer (thompsonJ P : Set Γ) ∨
        (oTwoUpper X ≤ Subgroup.centralizer
            (CFSG.Quasithin.omegaOneCenterOf (thompsonJi P j) : Set Γ) ∧
          X ≤ Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf (thompsonJi P j) : Set Γ))

@[expose] def E54L34FactSQTK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K P : Subgroup G), SQTKGroup ↥X →
    CharTwo X → IsSylowTwoOf P X → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    LieModel (O2Q K) .PSL 3 2 2 → X = K ⊔ P → X ⊓ centralizerModO2 K ≤ pCoreOf 2 X →
      X ≤ Subgroup.normalizer (thompsonJ P : Set G) ∨
        X ≤ Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf (thompsonJi P 4) : Set G)

end CFSG.Quasithin.H13
