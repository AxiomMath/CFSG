module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderFamilies

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringUnitary

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)
open CFSG.HardMathSupport.Lang.Coordinator (OuterFixedOrderBoundAt)

theorem false_of_outerBound {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n p : ℕ}
    (hb : OuterFixedOrderBoundAt t) (hadm : StatedLieAdmissible t n p 1)
    (hmodel : CFSG.Blueprint.LieModel X t n p 1) (ht : t ≠ .Tits)
    (hdiv : ¬ 3 ∣ lieOrderDivisor t n (p ^ 1)) (hD4 : ¬ (t = .POmegaPlus ∧ n = 4 ∧ 3 = 3))
    (htri : t ≠ .trialityD4) {α : MulAut X} (hα : α ^ 3 = 1)
    (hout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X) : False := by
  rcases hb X n p 1 hadm hmodel ht 3 Nat.prime_three (by norm_num) hdiv hD4 α hα hout with
    ⟨f₀, hf, -⟩ | ⟨h, -, -⟩
  · omega
  · exact htri h

end CFSG.RankThree.PartTwo.Sec4.HeringUnitary
