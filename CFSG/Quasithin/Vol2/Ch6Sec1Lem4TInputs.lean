module

public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public meta import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Quasithin.H13.Tits614

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def pWord : List ℤ := [1, -2, 3]

@[expose] def pArr : Array ℕ := wordArr 1755 titsHArrs pWord

@[expose] def pow5Arr (a : Array ℕ) : Array ℕ :=
  compA 1755 a (compA 1755 a (compA 1755 a (compA 1755 a a)))

@[expose] def eXWord (i : ℕ) : List ℤ := [[1], [1], [1], [1], [2]].getD i []

@[expose] def eYWord (i : ℕ) : List ℤ := [[1, 2], [1, 3], [1, 4], [2, 3], [1, 3]].getD i []

@[expose] def eXArr (i : ℕ) : Array ℕ := wordArr 1755 titsJArrs (eXWord i)

@[expose] def eYArr (i : ℕ) : Array ℕ := wordArr 1755 titsJArrs (eYWord i)

@[expose] def eGenArr (i : ℕ) : Array ℕ := commArr 1755 (eXArr i) (eYArr i)

@[expose] def eProdArr (v : ℕ) : Array ℕ :=
  (List.range 5).foldl (fun a i => if v.testBit i then compA 1755 a (eGenArr i) else a)
    (idA 1755)

@[expose] def eArrs : List (Array ℕ) := (List.range 32).map eProdArr

@[expose] def inE (a : Array ℕ) : Bool := anyEq eArrs a

@[expose] def inJ (a : Array ℕ) : Bool := siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 a

@[expose] def outerArr (a : Array ℕ) : Array ℕ := compA 1755 a titsGenArrs[1]!

end CFSG.Quasithin.H13.Tits614
