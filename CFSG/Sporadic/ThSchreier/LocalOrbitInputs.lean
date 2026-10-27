
module

public import CFSG.Sporadic.ThSchreier.LocalDataBase
public import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.LocalDataBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] def rowsLX : Array V4 := abRows xWord

@[expose] def rowsLY : Array V4 := abRows yWord

@[expose] def localPermX : Array ℕ := (natsOf (include_str "Data/LocalPermX.txt")).toArray

@[expose] def localPermY : Array ℕ := (natsOf (include_str "Data/LocalPermY.txt")).toArray

@[expose] def localTreePts : Array ℕ := (natsOf (include_str "Data/LocalTreePoints.txt")).toArray

@[expose] def localTreePar : Array ℕ := (natsOf (include_str "Data/LocalTreeParents.txt")).toArray

@[expose] def localTreeLab : Array ℕ := (natsOf (include_str "Data/LocalTreeLabels.txt")).toArray

@[expose] def localRowV4 (i : ℕ) : V4 := v4OfNat (localRowNats.getD i 0)

@[expose] def wKeyRow : Key :=
  canon (v4OfNat 0xb9318bc60b06215ff4eb15e228ba41526fe75848bd0133807208caa1fa8551)
    (v4OfNat 0x1e1057aa10c4abdf6972134ec61140ccf2027af03f80a7ed5002b65e4b1cca)

end CFSG.Sporadic.ThSchreier
