module

public import CFSG.Monster.B.Fischer.ArrCert
public import CFSG.RankThree.Native.DerivedGenerators
public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native

structure WitData where
  n : ℕ
  gens : Array (Array ℕ)
  nGens : ℕ
  pW : Array (List ℤ)
  pKeys : List ℕ
  pFuel : ℕ
  pOrd : ℕ
  qW : Array (List ℤ)
  qKeys : List ℕ
  qFuel : ℕ
  yW : Array (List ℤ)

@[expose] def parseSigned (s : String) : List ℤ :=
  s.toList.map fun c =>
    if 97 ≤ c.toNat then ((c.toNat - 96 : ℕ) : ℤ) else -((c.toNat - 64 : ℕ) : ℤ)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
