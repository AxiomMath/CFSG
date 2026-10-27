module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Assembly
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Comb
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7Cover
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7Transport

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos


theorem excU7_holds :
    ExcU7 :=
  excU7_of_pieces twE6U7C1_holds twE6U7C2_holds excNbrDictTwo_holds excU7Cover_holds
    excU7Transport_holds

end CFSG.StandardType.LieKnownR2.ExcPos
