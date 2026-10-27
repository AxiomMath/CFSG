module

public import CFSG.Quasithin.H13.L32ASetting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Input1476Shape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ Y : Subgroup G, oTwoUpper Y = Y → Y ≤ H →
      H ≤ Subgroup.normalizer (Y : Set G) → (∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y) →
      pCoreOf 2 Y < Y → Y ⊓ Subgroup.normalizer (L : Set G) = pCoreOf 2 Y →
      H = Y ⊔ (L32A.l1 T L V ⊔ T) →
      (∀ N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), N.Normal → N ≠ ⊥ → N ≤ modO2Image H Y →
        N = modO2Image H Y) →
      (pCoreOf 2 Y).relIndex Y = p ∧ H ≤ Subgroup.normalizer (L32A.l1 T L V : Set G) ∧
        ∀ t ∈ T, t * t ∈ pCoreOf 2 H → ∀ l ∈ L32A.l1 T L V,
          t * l * t⁻¹ * l⁻¹ ∈ pCoreOf 2 H

end CFSG.Quasithin.H13
