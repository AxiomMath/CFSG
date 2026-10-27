module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFact
import CFSG.GH74.Generic.BProg.B2.PumpupTableL2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Sect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem kFactL28_L2_odd {Q : Type} [Group Q] [Finite Q] {p f : ℕ} (hp : p ≠ 2)
    (hQ : LieModel Q .PSL 2 p f) {X W T : Subgroup Q} (c : KCfgL28 X W T) : False :=
  CFSG.LocalAnalysis.WeakClosure81.not_isCalL1_of_sectionalTwoRankLE_two
    (CFSG.GH74.Generic.BProg.B2.PumpupTableL2.sectionalTwoRankLE_two_of_psl2_model hp hQ) X
    (CFSG.pCore 2 ↥X) ⟨3, by decide, by decide, Or.inl c.isL2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
