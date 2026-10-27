module

public import CFSG.Quasithin.H13.StatementsFSU
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Background.G2A5Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

@[expose] def Stmt13_3_2_three_A5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), QTH13 G T L →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      quasithinO2QuotientIso K (alternatingGroup (Fin 5)) →
      ∀ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V →
        IsA5ModuleFor K (Subgroup.centralizer (V : Set G)) V

@[expose] def StmtF431U42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (M₁ M₂ : Subgroup G) (z : G),
      (IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups M₁ M₂) (IsLieOverTwo .PSU 4 1) ∨
        IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups M₁ M₂)) →
      pCoreOf 2 (M₁ ⊔ M₂) = ⊥ →
      z ^ 2 = 1 → z ≠ 1 → z ∈ centerOf (M₁ ⊓ M₂) →
      Subgroup.centralizer ({z} : Set G) ≤ M₁ →
      Subgroup.normalizer (centerOf (pCoreOf 2 M₁) : Set G) = M₁ →
      Subgroup.normalizer (centerOf (pCoreOf 2 M₂) : Set G) = M₂ →
      LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1

end CFSG.Quasithin.H13
