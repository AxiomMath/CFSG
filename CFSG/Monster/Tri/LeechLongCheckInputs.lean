module

public import CFSG.Monster.Tri.LeechCheckInputs
public import CFSG.Monster.Tri.LeechLongData

@[expose] public section

namespace CFSG.Monster.Tri.Leech

def treeNeOK (vs par : Array Nat) (w : Nat) : Bool :=
  (List.range vs.size).all fun i => i == 0 || (vs[i]! ^^^ vs[par[i]!]! != w)

def leechLongCheck : Bool :=
  treeOK shortKlev leechNbr leechLongPar leechLongLev && treeNeOK leechNbr leechLongPar 12288

end CFSG.Monster.Tri.Leech
