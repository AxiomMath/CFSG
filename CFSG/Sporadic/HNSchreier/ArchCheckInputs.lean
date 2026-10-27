module

public import CFSG.Sporadic.HNSchreier.OrbitCheck
public import CFSG.Sporadic.HNSchreier.HexDecode
public import CFSG.Sporadic.HNSchreier.HexKernel
public import CFSG.Sporadic.HNSchreier.ArchiveKernelData
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native

@[expose] def arraysPayload (_ : Unit := ()) : String :=
  Kernel.encodeBytes (archiveKernelBytes ()).bytes

theorem arraysPayload_decode : hexDumpBytes arraysPayload = (archiveKernelBytes ()).toByteArray :=
  Kernel.encodeBytes_decode _

@[expose] def le32 (B : ByteArray) (k : Nat) : Nat :=
  (B.get! k).toNat + 256 * (B.get! (k + 1)).toNat + 65536 * (B.get! (k + 2)).toNat +
    16777216 * (B.get! (k + 3)).toNat

@[noinline, expose] def archDataChecks (B : ByteArray) : Bool :=
  B.size == 12 + 8 * 1140000 &&
    ((List.range 8).map fun k => (B.get! k).toNat) == "HNPAIR01".toList.map Char.toNat &&
    le32 B 8 == 1140000 &&
    allIn 0 1140000 (fun i => decide (le32 B (12 + 8 * i) < 1140000) &&
      decide (le32 B (12 + 8 * i + 4) < 1140000))

@[noinline, expose] def archEqChecks (B : ByteArray) (O : VOrbit) : Bool :=
  allIn 0 1140000 (fun i => le32 B (12 + 8 * i) == ap O.alpha i &&
    le32 B (12 + 8 * i + 4) == ap O.beta i)

end CFSG.Sporadic.HNSchreier.Native
