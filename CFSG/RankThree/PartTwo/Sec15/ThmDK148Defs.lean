module

public import CFSG.RankThree.PartTwo.Sec15.ThmDDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

@[expose] noncomputable def Step148FourKFact' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), Y = deltaZero A (lB A) Y →
      ¬ CentralizesQuot A Y →
      Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) →
      (∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7))) →
      WStarS4 A → Print148FourK A Y

end CFSG.RankThree.PartTwo.Sec15.ThmD
