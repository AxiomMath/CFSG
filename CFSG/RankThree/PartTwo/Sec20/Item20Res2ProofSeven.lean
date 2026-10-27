module

public import CFSG.RankThree.PartTwo.Sec20.Step2054Proof
public import CFSG.RankThree.PartTwo.Sec20.OneFrontierCleanStatements

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Item206One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N → ⁅vTwenty M c T, A ⊓ L⁆ = ⊥

@[expose] def Step207E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    ¬ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    ⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ ≠ ⊥

@[expose] def Step207LE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    ¬ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    L ≤ Subgroup.centralizer
      ((⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ : Subgroup G) : Set G)

@[expose] def Step207K0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    ¬ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    ⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ ≠ ⊥ →
    L ≤ Subgroup.centralizer
      ((⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ : Subgroup G) : Set G) →
    kTwenty M c ≤ N

theorem item207One_of_steps (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053)
    (h189 : Sec18.Item189) (hE : Step207E) (hLE : Step207LE) (hK0 : Step207K0) :
    Item207One := by
  intro G _ _ A M L N c T hT hTN
  by_contra hne
  have h3 := h2053 G A M L N c T hT (rank3II_20_5_2_of h204 hT (h2051 G A M L N c T hT))
  obtain ⟨-, hKN, -⟩ := item189_case_one h189 hT h3
  exact hKN (hK0 G A M L N c T hT hTN hne (hE G A M L N c T hT hTN hne)
    (hLE G A M L N c T hT hTN hne))

end CFSG.RankThree.PartTwo.Sec20
