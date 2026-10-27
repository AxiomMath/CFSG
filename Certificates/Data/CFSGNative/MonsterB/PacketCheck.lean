module

public import Certificates.Data.CFSGNative.MonsterB.PacketData
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model

public section

namespace CFSG.Monster.B.Rep4371.Native

open CFSG.Monster.B.Native (packetRows packetLabels packetSpinIndices)

@[expose] def signCodes : Array Nat := #[3, 5, 9, 17, 33, 64, 129, 256, 512, 1024, 2048]

@[expose] def genAct (i : Nat) : Key → List (Key × Int) :=
  if i < 23 then keyActPauli (qPauli i)
  else if i < 35 then keyActPerm recPerms[i - 23]!
  else if i < 46 then keyActSign signCodes[i - 35]!
  else keyActXi

@[expose] def genCheck (i : Nat) : Bool := genOK (genAct i) packetRows[i]!

@[expose] def tauCheck (_ : Unit := ()) : Bool := (List.range 4371).all fun k => packetRows[47]![k]! == tauRow k

@[expose] def labelsCheck (_ : Unit := ()) : Bool :=
  (List.range 2300).all fun t =>
    match rawModel (23 + t) with
    | [(κ, _), (κ', _)] =>
      κ.1 == 1 && κ'.1 == 1 &&
        packetLabels[t]! == ((0, κ.2.1, κ.2.2), (0, κ'.2.1, κ'.2.2))
    | _ => false

@[expose] def spinIndexCheck (_ : Unit := ()) : Bool :=
  (List.range 2048).all fun t =>
    packetSpinIndices[t]! == (if 1024 ≤ t then 2048 else 0) + oddCodes[t % 1024]! / 2

end CFSG.Monster.B.Rep4371.Native
