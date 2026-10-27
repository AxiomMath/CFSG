module

public import CFSG.Quasithin.Vol2.Ch11SecE42Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Obl11_4_2S3Lie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G) (z : G),
    Conf11_4_2 T L I n V₁ z → quasithinIsMaximalLocal T (kz L V₁ z) →
    ¬ thompsonJ (ROf T L V₁) ≤ pCoreOf 2 (kz L V₁ z ⊔ T) →
    (IsSL3 (2 ^ n) (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∨
      IsPSL 3 2 n (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∨
      IsPSp4 2 n (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∨
      IsG2 2 n (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z))) → False

@[expose] def Obl11_4_2S3A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G) (z : G),
    Conf11_4_2 T L I n V₁ z → quasithinIsMaximalLocal T (kz L V₁ z) → n = 2 →
    ¬ thompsonJ (ROf T L V₁) ≤ pCoreOf 2 (kz L V₁ z ⊔ T) →
    (IsAlt 7 (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∨
      IsHat (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) (alternatingGroup (Fin 7))) → False

end CFSG.Quasithin.Vol2.Ch11.SecE
