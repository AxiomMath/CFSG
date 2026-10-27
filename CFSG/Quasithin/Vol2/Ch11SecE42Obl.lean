module

public import CFSG.Quasithin.Vol2.Ch11SecE42Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Obl11_4_2S1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G) (z : G),
    Conf11_4_2 T L I n V₁ z →
      ∀ Kp : Subgroup G, quasithinIsLocal T Kp → kz L V₁ z ≤ Kp → Kp = kz L V₁ z

@[expose] def Obl11_4_2S3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G) (z : G),
    Conf11_4_2 T L I n V₁ z → quasithinIsMaximalLocal T (kz L V₁ z) → False

end CFSG.Quasithin.Vol2.Ch11.SecE
