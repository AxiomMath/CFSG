module

public import Certificates.Data.CFSGNative.MonsterVis.Frame

public section

namespace CFSG.Monster.B.Short.Native

open CFSG.Monster.VisCert.Native

@[expose] def shortSeed (_ : Unit := ()) : Nat := 12288

@[expose] def shortCount (_ : Unit := ()) : Nat := 98280

structure ShortTables where
  klev : ByteArray
  klab : ByteArray
  kpar : ByteArray

@[expose] def shortTables (_ : Unit := ()) : ShortTables :=
  let tabs := frameRows.map fastTables
  let (klev, klab, kpar, _) := kSearch tabs shortSeed
  ⟨klev, klab, kpar⟩

@[inline, expose] def shortPointOK (T : ShortTables) (v : Nat) : Bool :=
  let l := rd8 T.klev v
  if l == 0 then true else
    if l == 1 then v == shortSeed else
      let p := rd32 T.kpar v
      let g := rd8 T.klab v
      p < 2 ^ 24 && g < 15 && rd8 T.klev p + 1 == l && gimg g p == v

@[expose] def shortCheck (T : ShortTables) (chunks : Nat) : Bool :=
  parAll (2 ^ 24) chunks (shortPointOK T) &&
    countBelow (fun v => rd8 T.klev v != 0) (2 ^ 24) == shortCount

@[expose] def shortCertOK (_ : Unit := ()) : Bool := shortCheck shortTables 8

end CFSG.Monster.B.Short.Native
