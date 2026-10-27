module

public import CFSG.Quasithin.Vol2.Ch12Sec2ChainStmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem12225YNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p → n ≠ 3 →
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer
          ((oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) : Subgroup G) :
            Set G)

@[expose] def Lem12225CTL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p → n = 3 →
      T ⊓ Subgroup.centralizer (L : Set G) = ⊥

@[expose] def Lem12225N5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p → n = 3 ∨ n = 4

@[expose] def Lem12226Split : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p →
      ∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L

end CFSG.Quasithin.H13
