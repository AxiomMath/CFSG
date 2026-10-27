module

public import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def titsRLevels : Array Level := rawLevels 1755 titsRArrs (baseArr 1755 titsRBase)

@[expose] def invWord (w : List ℤ) : List ℤ := w.reverse.map Neg.neg

@[expose] def provWord (u v w : List ℤ) : List ℤ :=
  invWord w ++ invWord u ++ invWord v ++ u ++ v ++ w

@[expose] def inS (a : Array ℕ) : Bool := siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 a

@[expose] def inR (a : Array ℕ) : Bool := siftA 1755 titsRLevels (baseArr 1755 titsRBase) 0 a

@[expose] def titsXArr : Array ℕ := wordArr 1755 titsDerivedArrs titsXWord

@[expose] def titsYArr : Array ℕ := wordArr 1755 titsDerivedArrs titsYWord

@[expose] def titsXYArr (i j : ℕ) : Array ℕ :=
  compA 1755 (Nat.iterate (compA 1755 titsXArr) i (idA 1755))
    (Nat.iterate (compA 1755 titsYArr) j (idA 1755))

end CFSG.Sporadic.Schreier.Tits
