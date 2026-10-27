module

public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.A6Setting134

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Stmt13_4_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (_ : A6.Setting134 G T L V)
    (H : Subgroup G), InH T H → ¬ H ≤ normalizer (L : Set G) → ¬ Group.IsSolvable ↥H →
    (∃ K : Subgroup G, K ∈ cComp H) ∧
    ∀ K ∈ cComp H,
      (quasithinIsMaximalLocal T K ∧ quasithinIsFaithfulLocal T K) ∧
      H ≤ normalizer (K : Set G) ∧
      (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
        LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 K) ∧
      ¬ K ≤ normalizer (L : Set G) ∧ ¬ L ≤ normalizer (K : Set G) ∧
      ¬ K ≤ centralizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) ∧
      (∀ W : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) K W →
        IsIrrPlusIn K (reducedAggregate H) K W) ∧
      (∃ VK : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T VK) ∧
      ∀ VK : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T VK →
        T ≤ normalizer (VK : Set G) ∧ FSU G T K VK ∧
        VK = conjClosure (quasithinOmegaOneCenter T ⊓ VK) K ∧
        (∃ _ : IsMulCommutative ↥VK,
          (AlternatingNatural (V := ↥VK) (autOn K VK) ⊤ ⊥ 5 ∧
              VK ⊓ centralizer (K : Set G) = ⊥) ∨
            (AlternatingNatural (V := ↥VK) (autOn K VK) ⊤ ⊥ 6 ∧
              VK ⊓ centralizer (K : Set G) = ⊥) ∨
            (Nat.card VK = 2 ^ 5 ∧ Nat.card ↥(VK ⊓ centralizer (K : Set G)) = 2 ∧
              FFModel.Realizes (V := ↥VK) (altCoreModel 6) (autOn K VK) ⊤ ⊥) ∨
            (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧
              BinaryNaturalSL (V := ↥VK) (autOn K VK) ⊤ ⊥ 3 1 ∧
              VK ⊓ centralizer (K : Set G) = ⊥)) ∧
        A6.o2Z K = K ⊓ centralizer (VK : Set G) ∧
        K ⊓ centralizer (reducedAggregate H : Set G) = A6.o2Z K

end CFSG.Quasithin.H13.NQS134
