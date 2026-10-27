module

public import Certificates.Data.Item434D42
public meta import Certificates.Data.Item434D42
public meta import Certificates.Data.K426Checks

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Fam3D42

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.RankThree.PartTwo.KFacts.K426

@[expose] def uWordA : List (Fin 3 × Bool) :=
  [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)]

@[expose] def uWordB : List (Fin 5 × Bool) := [(4, true)]

@[expose] def localUCheck (_ : Unit := ()) : Bool :=
  uFlag 2457 d4Lines[0]! (evalWA 2457 d4CAGens uWordA) &&
    uFlag 2457 d4Lines[1]! (evalWA 2457 d4CBGens uWordB)

end CFSG.HardMathSupport.Dickson.Bal207.Fam3D42
