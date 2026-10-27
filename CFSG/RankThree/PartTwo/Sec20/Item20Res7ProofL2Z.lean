module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofL2

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step204FinalL2ZNe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∃ m : ℕ, Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
        ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c →
          ¬ yTwenty X c ⊓ M ≤ kTwenty M c ⊔ oThreePrimeYR M X T c

theorem step204FinalL2Z_of_ne (h : Step204FinalL2ZNe) (hY : Step204YAlphaNe) :
    Step204FinalL2Z := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hL2
  exact h G A M L N c T i j P hset X hX hXM hm hL2 (hY G A M L N c T i j P hset X hX hXM hm)

end CFSG.RankThree.PartTwo.Sec20
