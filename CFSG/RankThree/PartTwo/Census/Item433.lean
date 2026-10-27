module

public import CFSG.RankThree.PartTwo.Census.Carrier.CasesAll
public import CFSG.RankThree.PartTwo.Census.Spin.Main
public import CFSG.RankThree.PartTwo.Census.Exceptional.Main
public import CFSG.RankThree.PartTwo.Census.Sporadic.Main

public section

namespace CFSG.RankThree.PartTwo.Census

theorem spinWitnessCases433 : SpinWitnessCases433 where
  typeB := Spin.spinWitness_typeB
  typeD := Spin.spinWitness_typeD
  typeTwistedD := Spin.spinWitness_typeTwistedD

theorem item433 : Item433 :=
  item433_of_carrierCases item433Case_sporadic spinWitnessCases433
    Exceptional.exceptionalWitnessCases433 carrierCases433

end CFSG.RankThree.PartTwo.Census
