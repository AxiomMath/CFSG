module

public import CFSG.RankThree.Native.Co3FiveArrays

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2

@[expose] def co3FiveQ : Subgroup (Equiv.Perm (Fin 276)) :=
  Subgroup.closure (permsA 276 co3FiveQGenArrs)

@[expose] def co3FiveLine (j : Fin 31) : Equiv.Perm (Fin 276) :=
  permOfArr 276 (co3FiveLineArr j)

@[expose] def co3FiveC0 : Subgroup (Equiv.Perm (Fin 276)) :=
  Subgroup.closure (permsA 276 co3FiveC0GenArrs)

@[expose] def co3FiveC25 : Subgroup (Equiv.Perm (Fin 276)) :=
  Subgroup.closure (permsA 276 co3FiveC25GenArrs)

@[expose] def co3FiveD : Subgroup (Equiv.Perm (Fin 276)) := ⁅co3FiveC0, co3FiveC0⁆

@[expose] def co3FiveA : Subgroup (Equiv.Perm (Fin 276)) :=
  Subgroup.closure (permsA 276 co3FiveAGenArrs)

@[expose] def co3FiveRecordOf (j : Fin 31) : Fin 31 := if (j : ℕ) = 25 then 25 else 0

@[expose] def co3FiveTransporter (j : Fin 31) : Equiv.Perm (Fin 276) :=
  permOfArr 276 (co3FiveHArr j)

end CFSG.RankThree.Native
