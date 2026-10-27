module

public import CFSG.RankThree.PartOne.S11d.PSLGood
public import CFSG.RankThree.PartOne.S11d.PSpDescent
public import CFSG.RankThree.PartOne.S11d.PSUDescent
public import CFSG.RankThree.PartOne.S11d.OrthGood
public import CFSG.RankThree.PartOne.S11d.LieGoodVacuous
public import CFSG.RankThree.PartOne.S11d.LieGoodTransfer
public import CFSG.RankThree.PartOne.KLC.Unconditional
public import CFSG.RankThree.PartOne.KEXC.OddCenterLie

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem lieGoodComponentFixT_all
    : ∀ t : StatedLieTag, LieGoodComponentFixT t := by
  intro t
  cases t
  · exact lieGoodComponentFixT_PSL
  · exact lieGoodComponentFixT_PSU
  · exact lieGoodComponentFixT_PSp
  · exact lieGoodComponentFixT_POmegaOdd
  · exact lieGoodComponentFixT_POmegaPlus
  · exact lieGoodComponentFixT_POmegaMinus
  · exact KLC.lieGoodComponentFixT_exceptional_unconditional (Or.inl rfl)
  · exact KLC.lieGoodComponentFixT_exceptional_unconditional (Or.inr (Or.inl rfl))
  · exact KLC.lieGoodComponentFixT_exceptional_unconditional (Or.inr (Or.inr (Or.inl rfl)))
  · exact KLC.lieGoodComponentFixT_exceptional_unconditional
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact KLC.lieGoodComponentFixT_exceptional_unconditional
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact KLC.lieGoodComponentFixT_exceptional_unconditional
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact KLC.lieGoodComponentFixT_exceptional_unconditional
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact lieGoodComponentFixT_twistedB2
  · exact lieGoodComponentFixT_twistedG2
  · exact KLC.lieGoodComponentFixT_exceptional_unconditional
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  · exact lieGoodComponentFixT_Tits

theorem lieGoodComponent_closed
    : LieGoodComponent :=
  lieGoodComponent_of_tags KEXC.oddCenterLie_holds lieGoodComponentFixT_all

end CFSG.RankThree.PartOne
