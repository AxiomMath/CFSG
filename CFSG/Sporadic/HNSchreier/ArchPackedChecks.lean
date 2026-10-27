module
public import CFSG.Sporadic.HNSchreier.PackedWordRead

public section
namespace CFSG.Sporadic.HNSchreier.Native.Kernel
open CFSG.Sporadic.Th.Native CFSG.Sporadic.F5.Native

@[expose] def archDataChecksPacked (width n : Nat) : Bool :=
  width == 12 + 8 * 1140000 &&
    ((List.range 8).map fun k => ((KernelBytes.packedFast width n).get k).toNat) ==
      "HNPAIR01".toList.map Char.toNat &&
    packedWordRead width n 8 == 1140000 &&
    allInKernel 0 1140000 (fun i => decide (packedWordRead width n (12 + 8 * i) < 1140000) &&
      decide (packedWordRead width n (12 + 8 * i + 4) < 1140000))

theorem archDataChecks_packed (width n : Nat) :
    archDataChecksKernel (KernelBytes.packedFast width n) = archDataChecksPacked width n := by
  simp only [archDataChecksKernel, archDataChecksPacked, le32Read_eq_packedWordRead]
  rfl

@[expose] def archEqChecksPacked (width n : Nat) (O : VOrbit) : Bool :=
  allInKernel 0 1140000 (fun i => packedWordRead width n (12 + 8 * i) == ap O.alpha i &&
    packedWordRead width n (12 + 8 * i + 4) == ap O.beta i)

theorem archEqChecks_packed (width n : Nat) (O : VOrbit) :
    archEqChecksKernel (KernelBytes.packedFast width n) O = archEqChecksPacked width n O := by
  simp only [archEqChecksKernel, archEqChecksPacked, le32Read_eq_packedWordRead]

end CFSG.Sporadic.HNSchreier.Native.Kernel
