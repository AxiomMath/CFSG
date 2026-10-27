module

public import CFSG.Monster.B.Fischer.HexadQuot
public import CFSG.Monster.B.Fischer.ArrCert
public meta import CFSG.Monster.B.Fischer.HexadQuot
public meta import CFSG.Monster.B.Fischer.ArrCert

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

@[expose] def gcatArr (i : ℕ) : Array ℕ :=
  if i = 0 then #[17, 19, 2, 3, 4, 20, 6, 11, 10, 9, 8, 7, 15, 14, 13, 12, 21, 0, 18, 1, 5, 16]
  else if i = 1 then #[0, 1, 19, 20, 18, 13, 14, 7, 8, 17, 12, 15, 10, 5, 6, 11, 16, 9, 4, 2, 3, 21]
  else #[19, 1, 9, 16, 21, 20, 15, 7, 11, 2, 10, 8, 18, 13, 14, 6, 3, 17, 12, 0, 5, 4]

@[expose] def cval (i : ℕ) : ℕ := if i = 0 then 9 else 0

@[expose] def alpha (i m : ℕ) : ℕ := linQ i m ^^^ cval i

@[expose] def alphaArr (i : ℕ) : Array ℕ := ((List.range 32).map (alpha i)).toArray

@[expose] def dGenArr (i : ℕ) : Array ℕ := gcatArr i ++ alphaArr i

@[expose] def dMul (s x : Array ℕ) : Array ℕ :=
  amulN (s.extract 0 22) (x.extract 0 22) ++ amulN (s.extract 22 54) (x.extract 22 54)

@[expose] def dAct (k : ℕ) (x : Array ℕ) : Array ℕ := dMul (dGenArr k) x

@[expose] def dValid (x : Array ℕ) : Bool :=
  x.size == 54 && PermArrN 22 (x.extract 0 22) && PermArrN 32 (x.extract 22 54)

@[expose] def dKey (x : Array ℕ) : ℕ := akeyN 22 (x.extract 0 22)

@[expose] def dRoot : Array ℕ := idArrN 22 ++ idArrN 32

@[expose] def dCert : ArrCert := arrBfs dAct 3 dKey dRoot 6000

end CFSG.Monster.B.Fischer
