module

public import CFSG.Quasithin.Vol2.Ch6Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

@[expose] def Parabolic6_1_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp6116 G T M L V n →
    (∃ H : Subgroup G, IsInHS T M L V H ∧ IsHStar T M H ∧
      Odd (critDist (L ⊔ T ⊔ H) (L ⊔ T) H V)) →
    IsMulCommutative ↥(conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) →
    ∃ P₁ : Subgroup G, P₁ ≤ Subgroup.normalizer (ch6ZS T L V : Set G) ∧
      T ≤ Subgroup.normalizer (P₁ : Set G) ∧ borelL T L ≤ Subgroup.normalizer (P₁ : Set G) ∧
      ¬ P₁ ≤ M ∧ IsSylowTwoOf (T ⊓ P₁) P₁ ∧ Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3))

end CFSG.Quasithin.H13
