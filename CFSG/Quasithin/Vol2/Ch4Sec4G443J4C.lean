module

public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def KG443J4GenM24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K Y V S : Subgroup G) (z : G),
    IsSporadic .J4 ↥K → Y ≤ K → ⁅Y, Y⁆ = Y → IsSporadic .M24 (↥Y ⧸ CFSG.pCore 2 ↥Y) →
    V ≤ centerOf (pCoreOf 2 Y) → V ≠ ⊥ → V = ⁅V, Y⁆ → IsSylowTwoOf S Y → z ∈ V → z ≠ 1 →
    z ∈ Subgroup.centralizer (S : Set G) →
    IsHat (↥(perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))) ⧸
        CFSG.pCore 2 ↥(perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))))
      (NativeSporadic.Carrier .M22) ∧
    K = Y ⊔ perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))

@[expose] def KG443J4GenL52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K Y V S : Subgroup G) (z : G),
    IsSporadic .J4 ↥K → Y ≤ K → ⁅Y, Y⁆ = Y → LieModel (↥Y ⧸ CFSG.pCore 2 ↥Y) .PSL 5 2 1 →
    V ≤ centerOf (pCoreOf 2 Y) → V ≠ ⊥ → V = ⁅V, Y⁆ → IsSylowTwoOf S Y → z ∈ V → z ≠ 1 →
    z ∈ Subgroup.centralizer (S : Set G) →
    IsHat (↥(perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))) ⧸
        CFSG.pCore 2 ↥(perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))))
      (NativeSporadic.Carrier .M22) ∧
    K = Y ⊔ perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))

@[expose] def KG443J4Loc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H L K B : Subgroup G),
    IsSQTKIn H → pCoreOf 2 H ≠ ⊥ → CharTwo H → L ∈ cComp H → K ≤ L →
    IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (NativeSporadic.Carrier .M22) → B ≤ H →
    B ≤ Subgroup.normalizer (L : Set G) → Nat.Coprime (Nat.card B) 6 →
    B ≤ Subgroup.centralizer (K : Set G) → ⁅L, B⁆ ≤ pCoreOf 2 L

end CFSG.Quasithin.H13.Ch4.G443J4
