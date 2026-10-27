module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.Assembly
import CFSG.OddTranspositions.PartThree.Eleven.Wong.PresRelators

public section

namespace CFSG.OddTranspositions.PartThree.Wong

theorem wongPSp4Five_holds : WongPSp4Five :=
  wongPSp4Five_of_relators fun _ _ _ D => D.constructed_generators_satisfy_relators.1

end CFSG.OddTranspositions.PartThree.Wong
