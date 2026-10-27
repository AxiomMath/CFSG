module

public import CFSG.RankThree.PartTwo.Sec19.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step1915W :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → L ≤ M →
      ∃ K ∈ oTwoComponentsIn M, L ≤ K ∧
        (K = L ⊔ CFSG.Open.pCoreOf 2 K ∨
          (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) p e ∧
            Sec4.IsoLThreePi (K ⧸ CFSG.pCore 2 K) p (3 * e) ∧
            KFacts.InducesStdKind K c .field) ∨
          (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) 2 n ∧
            CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ CFSG.pCore 2 K) .trialityD4 2 n ∧
            KFacts.InducesStdKind K c .graphField))

end CFSG.RankThree.PartTwo.Sec19
