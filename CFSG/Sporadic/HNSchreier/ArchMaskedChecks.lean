module
public import CFSG.Sporadic.HNSchreier.ArchPackedChecks
public section
namespace CFSG.Sporadic.HNSchreier.Native.Kernel
open CFSG.Sporadic.Th.Native CFSG.Sporadic.F5.Native

@[expose] def maskedWordRead (width n k : Nat) : Nat :=
  if k + 3 < width then 4294967295 &&& (n >>> (8*k))
  else le32Read (KernelBytes.packedFast width n).get k

theorem packedWordRead_eq_maskedWordRead (width n k : Nat) :
    packedWordRead width n k = maskedWordRead width n k := by
  unfold packedWordRead maskedWordRead
  split
  · exact (show (4294967295 &&& (n >>> (8*k))) = (n >>> (8*k)) % 4294967296 from by
      rw [Nat.and_comm]
      exact Nat.and_two_pow_sub_one_eq_mod _ 32).symm
  · rfl

@[expose] def archDataChecksMasked (width n : Nat) : Bool :=
  width == 12 + 8 * 1140000 &&
    ((List.range 8).map fun k => ((KernelBytes.packedFast width n).get k).toNat) ==
      "HNPAIR01".toList.map Char.toNat &&
    maskedWordRead width n 8 == 1140000 &&
    allInKernel 0 1140000 (fun i => decide (maskedWordRead width n (12 + 8 * i) < 1140000) &&
      decide (maskedWordRead width n (12 + 8 * i + 4) < 1140000))

@[expose] def archEqChecksMasked (width n : Nat) (O : VOrbit) : Bool :=
  allInKernel 0 1140000 (fun i => maskedWordRead width n (12 + 8 * i) == ap O.alpha i &&
    maskedWordRead width n (12 + 8 * i + 4) == ap O.beta i)


theorem archDataChecks_masked (width n : Nat) :
    archDataChecksPacked width n = archDataChecksMasked width n := by
  simp only [archDataChecksPacked, archDataChecksMasked, packedWordRead_eq_maskedWordRead]

theorem archEqChecks_masked (width n : Nat) (O : VOrbit) :
    archEqChecksPacked width n O = archEqChecksMasked width n O := by
  simp only [archEqChecksPacked, archEqChecksMasked, packedWordRead_eq_maskedWordRead]
end CFSG.Sporadic.HNSchreier.Native.Kernel
