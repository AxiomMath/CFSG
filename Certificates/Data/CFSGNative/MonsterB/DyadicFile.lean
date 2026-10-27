module

public import Certificates.Data.CFSGNative.MonsterB.DyadicData
public import Certificates.Data.CFSGNative.MonsterB.BinarySha

public section

namespace CFSG.Monster.B.Dyadic.Native

open CFSG.Monster.B.Binary.Native

@[expose, irreducible] def latticeSize (_ : Unit := ()) : Nat := 12 + 4 * (4371 * 4371)

@[expose] def latticeByte (rows : Array ByteArray) (pos : Nat) : UInt8 :=
  if pos < 12 then (u32le 1 ++ u32le 4371 ++ u32le 7).get! pos
  else if (pos - 12) % 4 = 0 then rows[(pos - 12) / 4 / 4371]!.get! ((pos - 12) / 4 % 4371)
  else 0

@[expose] def latticeFile (rows : Array ByteArray) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := latticeSize) fun pos => latticeByte rows pos.val)

@[expose] def latticeSha (_ : Unit := ()) : Nat :=
  0x66b790171e6dd45db2fdad110869458777d868d82f1f7bb1ba9081ebd6a8e4ac

@[expose] def latticeShaOK (_ : Unit := ()) : Bool := sha256Nat (latticeFile basisRows) == latticeSha

@[expose] def expCount (k : Nat) : Nat :=
  ((List.range dim).map fun i => if diagExp[i]! = k then 1 else 0).sum

@[expose] def expDefect (_ : Unit := ()) : Nat := ((List.range dim).map fun i => 7 - diagExp[i]!).sum

@[expose] def diagStatsOK (_ : Unit := ()) : Bool :=
  (List.range 8).map expCount == [0, 12, 284, 993, 1782, 1035, 243, 22] && expDefect == 13123

end CFSG.Monster.B.Dyadic.Native
