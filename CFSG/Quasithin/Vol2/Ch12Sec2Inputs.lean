module

public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.H13.StatementsVocab

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped IsMulCommutative

@[expose] def IrrPlusBaseNonempty : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G) →
      ∃ I : Subgroup G, IsIrrPlusBase L (reducedAggregate (L ⊔ T)) I

@[expose] def Stmt3_2_2_eight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ →
    conjClosure V₀ T ≤ conjClosure L T ⊔ T ∧
    IsPrimeReduced 2 ((conjClosure V₀ T).subgroupOf (conjClosure L T ⊔ T)) ∧
    pCoreOf 2 (conjClosure L T ⊔ T) = T ⊓ Subgroup.centralizer (conjClosure V₀ T : Set G)

@[expose] def G2ZornQuotientModel : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.IsQuasisimple Q → Odd (Nat.card (Subgroup.center Q)) →
    ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 2 ^ n → 1 ≤ n →
      ∀ φ : Q →* ↥⁅quasithinG2 K, quasithinG2 K⁆, Function.Surjective φ →
        (n = 1 → LieModel Q .PSU 3 3 1) ∧ (2 ≤ n → LieModel Q .G2 0 2 n)

@[expose] def NaturalSL24NotA5Sum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V : Subgroup G) [IsMulCommutative ↥V],
    L ≤ Subgroup.normalizer (V : Set G) →
    BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ((Subgroup.centralizer (L : Set G)).subgroupOf V) 2 2 →
    (∀ J : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ J → J ≤ V →
      L ≤ Subgroup.normalizer (J : Set G) → J = V ⊓ Subgroup.centralizer (L : Set G) ∨ J = V) →
      ¬ IsA5ModuleSum L V

@[expose] def L32FourIndecomposable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V : Subgroup G) [IsMulCommutative ↥V],
    L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V → V ≠ ⊥ → Nat.card V = 2 ^ 4 →
    BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ((Subgroup.centralizer (L : Set G)).subgroupOf V) 3 1 →
    (∀ J : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ J → J ≤ V →
      L ≤ Subgroup.normalizer (J : Set G) → J = V ⊓ Subgroup.centralizer (L : Set G) ∨ J = V) →
      IsIndecomposableUnder L V

@[expose] def HatA6SixIrreducible : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 6 →
    ∀ H : Subgroup (MulAut V), Group.IsPerfect ↥H → Nat.card (Subgroup.center ↥H) = 3 →
      Nonempty (↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin 6)) →
        fixV H = ⊥ ∧ ∀ W : Subgroup V, (∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def L52TenFixedPointFree : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 10 →
    ∀ H : Subgroup (MulAut V), Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
      commV H = ⊤ →
      (∀ W : Subgroup V, fixV H ≤ W → (∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) →
        W = fixV H ∨ W = ⊤) →
        fixV H = ⊥

@[expose] def ExtSqFourAltEight : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (U Z : Subgroup V), SLExteriorTwo H U Z 4 →
      AlternatingNatural H U Z 8

end CFSG.Quasithin.H13
