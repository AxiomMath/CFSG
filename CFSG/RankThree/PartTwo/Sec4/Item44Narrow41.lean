module

public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Three
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Item4_4OTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → Group.IsPerfect G →
    ∀ (K : Subgroup G) [K.Normal], Group.IsSolvable K → IsSimpleGroup (G ⧸ K) →
      CFSG.pCore 2 G ≠ ⊥ →
      IsQuasisimple (G ⧸ CFSG.pCore 2 G) ∨
      Nonempty (G ⧸ oTwoFitting G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∨
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧
        Nonempty (G ⧸ oTwoP p G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) ∨
      (Nonempty (G ⧸ oTwoP 3 G ≃* projSL 3 (GaloisField 3 1)) ∨
        IsExtOf (G ⧸ oTwoP 3 G) (alternatingGroup (Fin 5)) Q8D8)

theorem item4_4OTwo_holds :
    Item4_4OTwo := by
  intro G _ _ hG hperf K _ hK hsimple hO2
  have := hperf
  have := hsimple
  exact Census.rank3II_4_4_partOne Census.primeThreeLinear hG hK hO2

end CFSG.RankThree.PartTwo.Sec4
