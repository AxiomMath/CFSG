module
public import CFSG.Sporadic.HNSchreier.ArchCheckInputs

public section
namespace CFSG.Sporadic.HNSchreier.Native.Kernel
open CFSG.Sporadic.Th.Native CFSG.Sporadic.F5.Native

@[expose] def allInKernel (lo hi : Nat) (p : Nat → Bool) : Bool :=
  Nat.allTR (hi - lo) fun k _ => p (lo + k)

theorem allIn_kernel (lo hi : Nat) (p : Nat → Bool) :
    allIn lo hi p = allInKernel lo hi p := by
  unfold allIn allInKernel
  rw [Nat.all_eq_allTR]

@[expose] def le32Read (get : Nat → UInt8) (k : Nat) : Nat :=
  (get k).toNat + 256 * (get (k+1)).toNat + 65536 * (get (k+2)).toNat +
    16777216 * (get (k+3)).toNat

theorem le32_toByteArray (B : KernelBytes) (k : Nat) :
    le32 B.toByteArray k = le32Read B.get k := by
  simp only [le32, le32Read, KernelBytes.get_toByteArray]

@[expose] def archDataChecksKernel (B : KernelBytes) : Bool :=
  B.size == 12 + 8 * 1140000 &&
    ((List.range 8).map fun k => (B.get k).toNat) == "HNPAIR01".toList.map Char.toNat &&
    le32Read B.get 8 == 1140000 &&
    allInKernel 0 1140000 (fun i => decide (le32Read B.get (12 + 8 * i) < 1140000) &&
      decide (le32Read B.get (12 + 8 * i + 4) < 1140000))

theorem archDataChecks_kernel (B : KernelBytes) :
    archDataChecks B.toByteArray = archDataChecksKernel B := by
  simp only [archDataChecks, archDataChecksKernel, KernelBytes.size_toByteArray,
    KernelBytes.get_toByteArray, le32_toByteArray, allIn_kernel]

@[expose] def archEqChecksKernel (B : KernelBytes) (O : VOrbit) : Bool :=
  allInKernel 0 1140000 (fun i => le32Read B.get (12 + 8 * i) == ap O.alpha i &&
    le32Read B.get (12 + 8 * i + 4) == ap O.beta i)

theorem archEqChecks_kernel (B : KernelBytes) (O : VOrbit) :
    archEqChecks B.toByteArray O = archEqChecksKernel B O := by
  simp only [archEqChecks, archEqChecksKernel, le32_toByteArray, allIn_kernel]

end CFSG.Sporadic.HNSchreier.Native.Kernel
