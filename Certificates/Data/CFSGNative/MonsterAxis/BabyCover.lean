module

public import Certificates.Data.CFSGNative.MonsterAxis.Cover
public import Certificates.Data.CFSGNative.MonsterB.Short

public section

namespace CFSG.Monster.AxisCount.Native

open CFSG.Monster.AxisCount.Native.Cover

namespace Baby

@[expose] def lamBeta (_ : Unit := ()) : Nat := 12288

@[expose] def babyCount (_ : Unit := ()) : Nat := 46575

@[expose] def frameLev (_ : Unit := ()) : ByteArray := CFSG.Monster.VisCert.Native.frameTables.klev

@[expose] def shortLev (_ : Unit := ()) : ByteArray := CFSG.Monster.B.Short.Native.shortTables.klev

@[expose] def inDp (v : Nat) : Bool :=
  rd8 frameLev v != 0 && rd8 shortLev (v ^^^ lamBeta) != 0

@[inline, expose] def cvOKm (m : Nat) (T : CoverTables) (rows : Array (Array Nat))
    (seeds : Array Nat) (v : Nat) : Bool :=
  let o := rd8 T.lab v
  if o == 0 then true else
    let l := rd8 T.lev v
    o ≤ seeds.size &&
    (if l == 1 then v == seeds[o - 1]! else
      let p := rd32 T.par v
      let g := rd8 T.gen v
      l != 0 && p < 2 ^ 24 && g < m && rd8 T.lab p == o && rd8 T.lev p + 1 == l &&
        cvImg rows g p == v) &&
    allFrom (fun j => rd8 T.lab (cvImg rows j v) == o) 0 m

@[expose] def coverCheckM (m total : Nat) (T : CoverTables) (rows : Array (Array Nat))
    (seeds sizes : Array Nat) (chunks : Nat) : Bool :=
  rows.size == m && rows.all (fun r => r.size == 24 && r.all (fun x => x < 2 ^ 24)) &&
  seeds.size == sizes.size && seeds.size < 255 &&
  parAll (2 ^ 24) chunks (cvOKm m T rows seeds) &&
  countBelow (fun v => rd8 T.lab v != 0) (2 ^ 24) == total &&
  parAll seeds.size chunks
    (fun r => countBelow (fun v => rd8 T.lab v == r + 1) (2 ^ 24) == sizes[r]!) &&
  allFrom (fun r => seeds[r]! < 2 ^ 24 && rd8 T.lab seeds[r]! == r + 1) 0 seeds.size

@[expose, noinline] def orbitCheckM (us : List (List Gen)) (hs : List (List Gen))
    (lams sizes : List Nat) : Bool :=
  let rows : Array (Array Nat) := (us.map wordRows).toArray
  let seeds := lams.toArray
  let T := coverSearch (rows.map fastTables) seeds
  us.all (fun w => w.all Gen.isVis) && hs.all (fun w => w.all Gen.isVis) &&
  hs.length == lams.length && lams.length == sizes.length &&
  (hs.zip lams).all (fun x => l2Word x.1 x.2 == seedF) &&
  coverCheckM us.length babyCount T rows seeds sizes.toArray 3 &&
  parAll (2 ^ 24) 3 (fun v => !inDp v || rd8 T.lab v != 0)

end Baby

end CFSG.Monster.AxisCount.Native
