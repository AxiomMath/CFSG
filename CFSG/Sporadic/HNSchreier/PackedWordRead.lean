module

public import CFSG.Sporadic.HNSchreier.ArchKernelChecks
public import CFSG.Sporadic.HNSchreier.PackedKernelBytes

public section

namespace CFSG.Sporadic.HNSchreier.Native.Kernel

private theorem four_bytes (x : Nat) :
    x % 256 + 256 * (x / 256 % 256) + 65536 * (x / 65536 % 256) +
      16777216 * (x / 16777216 % 256) = x % 4294967296 := by
  have h₁ := Nat.mod_mul (a := 256) (b := 16777216) (x := x)
  have h₂ := Nat.mod_mul (a := 256) (b := 65536) (x := x / 256)
  have h₃ := Nat.mod_mul (a := 256) (b := 256) (x := x / 256 / 256)
  simp only [Nat.div_div_eq_div_mul] at h₁ h₂ h₃
  rw [h₂, h₃] at h₁
  omega

private theorem get_packedFast_toNat (width n k : Nat) (hk : k < width) :
    ((KernelBytes.packedFast width n).get k).toNat = n / 256 ^ k % 256 := by
  simp only [KernelBytes.packedFast, hk, ite_eq_left, UInt8.toNat_ofNat',
    Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem le32Read_packedFast (width n k : Nat) (hk : k + 3 < width) :
    le32Read (KernelBytes.packedFast width n).get k =
      (n >>> (8 * k)) % 4294967296 := by
  have h₀ : k < width := by omega
  have h₁ : k + 1 < width := by omega
  have h₂ : k + 2 < width := by omega
  simp only [le32Read, get_packedFast_toNat width n k h₀,
    get_packedFast_toNat width n (k + 1) h₁,
    get_packedFast_toNat width n (k + 2) h₂,
    get_packedFast_toNat width n (k + 3) hk,
    Nat.shiftRight_eq_div_pow, Nat.pow_mul, Nat.pow_add,
    ← Nat.div_div_eq_div_mul]
  exact four_bytes (n / 256 ^ k)

@[expose] def packedWordRead (width n k : Nat) : Nat :=
  if k + 3 < width then (n >>> (8 * k)) % 4294967296
  else le32Read (KernelBytes.packedFast width n).get k

theorem le32Read_eq_packedWordRead (width n k : Nat) :
    le32Read (KernelBytes.packedFast width n).get k = packedWordRead width n k := by
  unfold packedWordRead
  split
  · exact le32Read_packedFast width n k ‹_›
  · rfl

end CFSG.Sporadic.HNSchreier.Native.Kernel
