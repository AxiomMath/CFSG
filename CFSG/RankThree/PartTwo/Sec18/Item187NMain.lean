module

public import CFSG.RankThree.PartTwo.Sec18.Item187
public import CFSG.RankThree.PartTwo.Sec18.Item187NCaseI
public import CFSG.RankThree.PartTwo.Sec18.Item187NCaseII

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)


variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

theorem MinCex.false_of_not_isSolvable (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (h186 : Item186H) (hX : MinCex A M H c X)
    (hns : ¬ Group.IsSolvable ↥X) : False := by
  by_cases hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥
  · exact hX.false_of_pCore_eq_bot h1812 h184 h1842 h186 hns hO
  · exact hX.false_of_pCore_ne_bot h186 hns hO

theorem item187_nsol (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (h186 : Item186H) :
    ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G) (X : Subgroup G),
      MinCex A M H c X → ¬ Group.IsSolvable ↥X → False :=
  fun _ _ _ _ _ _ _ _ hX hns => hX.false_of_not_isSolvable h1812 h184 h1842 h186 hns

theorem item187_of_five_case (h1812 : Item181_2) (h1813 : Item181_3)
    (h184 : Item184_1) (h1842 : Item184_2) (h186 : Item186H)
    (h5 : ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G) (X : Subgroup G),
      MinCex A M H c X → Group.IsSolvable ↥X → 5 ∣ Nat.card X → False) : Item187 :=
  item187_of_cases h1813 h184 h186 h5 (item187_nsol h1812 h184 h1842 h186)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
