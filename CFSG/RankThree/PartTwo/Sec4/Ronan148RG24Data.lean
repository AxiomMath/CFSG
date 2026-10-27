module

public import CFSG.LieType.Multipliers.G24Data

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R.G24P

open CFSG.LieType.Multipliers.G24 CFSG.Fischer CFSG.Blueprint.Chevalley

@[expose] def z0Word : List (Fin 6 × Bool) :=
  genWordX ⟨1, by decide⟩ 1 ++ genWordY ⟨1, by decide⟩ 1

@[expose] def p1Word : List (Fin 6 × Bool) := parseWord "gdbgabcdbcbedcbgbacdcb"

@[expose] def p2Word : List (Fin 6 × Bool) := parseWord "gbgeabacdbcbaedgbacbadcbdg"

@[expose] def z0Arr (_ : Unit := ()) : Array (Array F4) := wordArr z0Word

@[expose] def p1Arr (_ : Unit := ()) : Array (Array F4) := wordArr p1Word

@[expose] def p2Arr (_ : Unit := ()) : Array (Array F4) := wordArr p2Word

end CFSG.RankThree.PartTwo.Sec4.Ronan148R.G24P

end
