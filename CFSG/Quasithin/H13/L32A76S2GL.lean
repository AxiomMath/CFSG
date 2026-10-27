module

public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.H13.L32ASetting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Input1476S2GL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ Y : Subgroup G, oTwoUpper Y = Y → Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) →
      (∀ y ∈ Y, y ^ 5 ∈ pCoreOf 2 Y) → Y ⊓ Subgroup.normalizer (L : Set G) = pCoreOf 2 Y →
      H = Y ⊔ (L32A.l1 T L V ⊔ T) → H ≤ Subgroup.normalizer (L32A.l1 T L V : Set G) →
      (∀ N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), N.Normal → N ≠ ⊥ → N ≤ modO2Image H Y →
        N = modO2Image H Y) → (pCoreOf 2 Y).relIndex Y = 25 →
      ∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
        mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)) = 1 →
        mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) = 1 →
        Nat.card ↥(⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) = 8 →
        fsuV1 T V ≤ ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ →
        F8.A₁ (fsuV1 T V) (g : G) ≤ ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ →
        autOn (Subgroup.normalizer ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G))
          ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ = ⊤

end CFSG.Quasithin.H13

end
