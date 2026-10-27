module

public import Certificates.Data.CFSGNative.MonsterAxis.CoPair
public import Certificates.Data.CFSGNative.F4.T46Simple
public import Certificates.Data.CFSGNative.McL.Certificate

public section

namespace CFSG.Monster.Existence.CoPair.Native

open CFSG.Sporadic.Th.Native (ap)
open CFSG.F4.Native (t46XT t46YT)

set_option compiler.extract_closed false

@[expose] def seedW1 (_ : Unit := ()) : Nat := 1

@[expose] def seedW2 (_ : Unit := ()) : Nat := 4096

@[expose] def orbW1OK (_ : Unit) : Bool := orbCheck seedW1 47104 (orbSearch seedW1) 8

@[expose] def orbW2OK (_ : Unit) : Bool := orbCheck seedW2 4600 (orbSearch seedW2) 8

@[expose] def u62WordA (_ : Unit := ()) : List Nat :=
  [1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1]

@[expose] def u62WordB (_ : Unit := ()) : List Nat :=
  [0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0]

@[expose] def u62Seed (_ : Unit := ()) : Nat := 6

@[expose] def u62J0 (_ : Unit := ()) : Nat := 152

@[expose] def u62Tables (_ : Unit) : EqTables :=
  eqSearch u62WordA u62WordB (ap t46XT) (ap t46YT) 693 u62Seed u62J0

@[expose] def u62OK (_ : Unit) : Bool :=
  eqCheck u62WordA u62WordB (ap t46XT) (ap t46YT) 693 (u62Tables ()) 8 &&
    actXY u62WordA seedW2 == seedW2 && actXY u62WordB seedW2 == seedW2

@[expose] def mclWordA (_ : Unit := ()) : List Nat :=
  [1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]

@[expose] def mclWordB (_ : Unit := ()) : List Nat :=
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0,
    1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0]

@[expose] def mclSeed (_ : Unit := ()) : Nat := 2

@[expose] def mclJ0 (_ : Unit := ()) : Nat := 185

@[expose] def mclTables (_ : Unit) : EqTables :=
  eqSearch mclWordA mclWordB (ap (CFSG.Sporadic.McL.Native.orbitData ()).alpha)
    (ap (CFSG.Sporadic.McL.Native.orbitData ()).beta) 275 mclSeed mclJ0

@[expose] def mclOK (_ : Unit) : Bool :=
  eqCheck mclWordA mclWordB (ap (CFSG.Sporadic.McL.Native.orbitData ()).alpha)
    (ap (CFSG.Sporadic.McL.Native.orbitData ()).beta) 275 (mclTables ()) 8 &&
    actXY mclWordA seedW1 == seedW1 && actXY mclWordB seedW1 == seedW1

end CFSG.Monster.Existence.CoPair.Native
