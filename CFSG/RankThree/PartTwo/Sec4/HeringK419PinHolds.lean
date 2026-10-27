module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinGlueX
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldPSp
public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinGlueY3

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)

theorem k419PinPSL_holds
    : K419PinPSL := by
  intro n F _ _ hn hlist
  by_contra hnp
  obtain ⟨p, e, hp, he, hq, -⟩ := HeringPin.exists_prime_pow_of_not_prime hnp
  exact HeringPin.not_numList46 hp he (HeringPin.xord_projectiveSL hn hq)
    (HeringPin.numList46_of_isList46 hlist)

theorem k419PinSL_holds
    : K419PinSL := by
  intro n F _ _ hn hlist
  by_contra hnp
  obtain ⟨p, e, hp, he, hq, -⟩ := HeringPin.exists_prime_pow_of_not_prime hnp
  exact HeringPin.not_numList46 hp he (HeringPin.xord_SL hn hq)
    (HeringPin.numList46_of_isList46 hlist)

theorem k419PinPSp_holds
    : K419PinPSp := by
  intro r F _ _ hr hlist
  by_contra hnp
  obtain ⟨p, e, hp, he, hq, hpc⟩ := HeringPin.exists_prime_pow_of_not_prime hnp
  exact HeringPin.not_numList46 hp he (HeringPin.xord_PSp hr hpc hq)
    (HeringPin.numList46_of_isList46 hlist)

theorem k419OneFieldPSL_holds
    : K419OneFieldPSL :=
  k419OneFieldPSL_of_pin k419PinPSL_holds

theorem k419OneFieldSL_holds
    : K419OneFieldSL :=
  k419OneFieldSL_of_pin k419PinSL_holds

theorem k419OneFieldPSp_holds
    : K419OneFieldPSp :=
  k419OneFieldPSp_of_pin k419PinPSp_holds

end CFSG.RankThree.PartTwo.Sec4
