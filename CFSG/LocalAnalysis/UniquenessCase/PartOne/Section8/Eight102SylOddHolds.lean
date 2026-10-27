module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102SylOddSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem kU4SylOdd_holds : KU4SylOdd := by
  intro X _ _ n hU4 hn q p hq hp hqn hpn
  obtain ⟨⟨h2, hn1, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    hU4.statedClassicalModel_of_ne_zero (by norm_num)
  let fieldK : Field K := hfield
  let finiteK : Finite K := hfinite
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    ⟨h2, hn1, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  exact (sylOddConcl_statedSU_four h hn hq hp hqn hpn).of_mulEquiv e

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
