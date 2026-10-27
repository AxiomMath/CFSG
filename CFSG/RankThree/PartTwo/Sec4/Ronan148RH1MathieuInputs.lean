module

public import CFSG.Sporadic.Schreier.M11Data
public import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.M11Data
public meta import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG.Sporadic.Schreier

@[expose] def mathieuNoFifteenCheck (_ : Unit := ()) : Bool :=
  (orderTables m11Certificate 15).length == 0 && (orderTables m12Certificate 15).length == 0

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
