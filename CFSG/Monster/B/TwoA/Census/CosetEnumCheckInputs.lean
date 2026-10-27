module

public import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.CosetCertData
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import Certificates.Data.CFSGNative.MonsterB.CosetEnum

public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster.B.Rep4371

@[expose] def cosetRec (i : ℕ) : Option CosetRecord := cosetData.find? (·.index == i)

@[expose] def cosetOrbits (i : ℕ) : List OrbitRecord :=
  ((cosetRec i).map CosetRecord.orbits).getD []

@[expose] def classEnc (k : ℕ) : ℕ := ((cosetOrbits 1).map OrbitRecord.rep).getD k 0

@[expose] def classSize (k : ℕ) : ℕ := ((cosetOrbits 1).map OrbitRecord.size).getD k 0

@[irreducible] def classCert (i root : ℕ) : NatCert :=
  natBfs (Native.CosetEnum.act (imgs i)) 24 root 9000

@[expose] def classCheck : Bool :=
  let a := tT 1
  let b := tD 1
  (List.range 137).all fun k =>
    let c := classCert 1 (classEnc k)
    natCertOK (Native.CosetEnum.act (imgs 1)) 24 (fun n => decide (n < 2 ^ 25)) (classEnc k)
        c &&
      c.pts.size == classSize k &&
      (List.range c.pts.size).all (fun j => decide (classEnc k ≤ c.pts[j]!)) &&
      Native.CosetEnum.sqTest a b (wP 1) (classEnc k)

@[expose] def class17Check : Bool :=
  let c := classCert 1 (classEnc 17)
  (List.range c.pts.size).any fun j => c.pts[j]! == 196668

@[expose] def class2Check : Bool :=
  let c := classCert 2 734
  natCertOK (Native.CosetEnum.act (imgs 2)) 24 (fun n => decide (n < 2 ^ 25)) 734 c &&
    c.pts.size == 8192 && Native.CosetEnum.sqTest (tT 2) (tD 2) (wP 2) 734

end CFSG.Monster.B.TwoA.Census
