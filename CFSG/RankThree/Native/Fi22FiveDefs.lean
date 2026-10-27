module

public import CFSG.RankThree.Native.Fi22FiveArrays
public import CFSG.Assembly.Defs

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer

@[expose] def fi22FiveQ : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure (permsA 3510 fi22FiveQGenArrs)

@[expose] def fi22FiveLine (i : Fin 6) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (fi22FiveLineArr i)

@[expose] def fi22FiveW : Equiv.Perm (Fin 3510) := permOfArr 3510 fi22FiveWArr

@[expose] def fi22FiveC (i : Fin 6) : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure (permsA 3510 (fi22FiveCGenArrs i))

@[expose] def fi22FiveD (i : Fin 6) : Subgroup (Equiv.Perm (Fin 3510)) :=
  ⁅fi22FiveC i, fi22FiveC i⁆

end CFSG.RankThree.Native
