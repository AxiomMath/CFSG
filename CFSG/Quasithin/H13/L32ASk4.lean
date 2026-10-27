module

public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.L32ASetting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ I : Subgroup G, fsuV1 T V ≤ I → I < conjClosure V H →
      H ≤ Subgroup.normalizer (I : Set G) →
      ∀ Y V₂ : Subgroup G, A6.IsV2 T V V₂ → Y ≤ H → oTwoUpper Y = Y →
        T ≤ Subgroup.normalizer (Y : Set G) →
        quasithinO2QuotientIso (Y ⊔ T) (Equiv.Perm (Fin 3)) →
        V ⊓ I = fsuV1 T V ∧
          (I.relIndex (conjClosure V₂ Y ⊔ I) = 2 ∨ I.relIndex (conjClosure V₂ Y ⊔ I) = 4) ∧
          (⁅V₂, Y⁆ ≤ I → ⁅V₂, Y⁆ = ⊥)

@[expose] def Lemma14_7_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    (modO2Image H (L32A.l1 T L V)).Normal →
    (∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
      F8.Dγ V (fsuV1 T V) H (g : G) < F8.Uγ V H (g : G) ∧
        ⁅F8.Uγ V H (g : G), L32A.l1 T L V⁆ ≤ pCoreOf 2 H) ∧
    pCoreOf 2 (L ⊔ T) ⊔ pCoreOf 2 H = pCoreOf 2 (L32A.l1 T L V ⊔ T) ∧
    Nat.card ↥(modO2Image H (L32A.l1 T L V)) = 3 ∧
    modO2Image H (pCoreOf 2 (L32A.l1 T L V ⊔ T)) = modO2Image H (pCoreOf 2 (L ⊔ T)) ∧
    modO2Image H (pCoreOf 2 (L32A.l1 T L V ⊔ T)) =
      modO2Image H T ⊓ Subgroup.centralizer (modO2Image H (L32A.l1 T L V) : Set _) ∧
    (modO2Image H (pCoreOf 2 (L32A.l1 T L V ⊔ T))).relIndex (modO2Image H T) = 2 ∧
    ⁅conjClosure V H, L32A.l1 T L V⁆ ⊔ fsuV1 T V = conjClosure V H

@[expose] def Lemma14_7_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    (modO2Image H (L32A.l1 T L V)).Normal →
    CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥

end CFSG.Quasithin.H13
