module

public import CFSG.Quasithin.H13.U3L14Blk

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def C137Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L P M : Subgroup G),
    CharTwo X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
    L ∈ cComp X → CharTwo L →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∨
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 ∨ autOn T V ≤ autOn L V) →
    T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) →
    (P = M ∨ (A6.IsHatA6 L ∧ P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ A6.o2Z L)) →
    IsTwoReducedIn X V → ⁅V, L⁆ ≠ ⊥ →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 →
      Nat.card ↥⁅V, L⁆ = 8 ∧ ∃ u ∈ ⁅V, L⁆, u ≠ 1 ∧ P = X ⊓ centralizer ({u} : Set G)) →
    CharNormal (baum (pCoreOf 2 P)) X ∨
      ((LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 → IsLnBlock L 3) ∧
        (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) → H13.IsA6Block L) ∧
        (A6.IsHatA6 L → H13.IsHatA6Block L) ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → H13.IsG2Block L)) ∨
      (Nat.card ↥(autOn X V) = 12096 ∧ ∃ l : Subgroup G, V ⊓ centralizer (L : Set G) ≤ l ∧
        l ≤ V ∧ Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
        P ≤ normalizer (l : Set G)) ∨
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L)

@[expose] def Stmt13_2_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V Lp : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → V ⊓ centralizer (L : Set G) = ⊥ →
    (A6.IsHatA6 L → Lp = A6.l1plus T L V) → (¬ A6.IsHatA6 L → Lp = L₁Of L (fsuV1 T V)) →
    Nonempty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 6))) →
      CharNormal (baum (pCoreOf 2 (Lp ⊔ T))) (L ⊔ T) ∨ H13.IsA6Block L

@[expose] def Stmt13_3_10G2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V Lp : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → V ⊓ centralizer (L : Set G) = ⊥ →
    Lp = L₁Of L (fsuV1 T V) → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → H13.IsG2Block L →
      normalizer (baum (pCoreOf 2 (Lp ⊔ T)) : Set G) ≤ normalizer (L : Set G)

end CFSG.Quasithin.H13.U3
