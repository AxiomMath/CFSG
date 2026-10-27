module

public import CFSG.Sporadic.HNSchreier.KernelBytes

public section

namespace CFSG.Sporadic.HNSchreier.KernelBytes

private theorem packed_low (a b l i : Nat) (hi : i < l) :
    UInt8.ofNat ((a + b * 256 ^ l) / 256 ^ i) = UInt8.ofNat (a / 256 ^ i) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ l by omega)
  have hp : 256 ^ l = 256 ^ i * (256 * 256 ^ k) := by
    rw [hk, Nat.pow_add, Nat.pow_add]
    simp only [Nat.pow_one, Nat.mul_assoc]
  rw [hp]
  have he : b * (256 ^ i * (256 * 256 ^ k)) = 256 ^ i * (256 * (b * 256 ^ k)) := by
    simp only [Nat.mul_left_comm]
  rw [he, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide))]
  rw [← UInt8.ofNat_mod_size, Nat.add_mul_mod_self_left]
  exact UInt8.ofNat_mod_size

private theorem packed_high (a b l j : Nat) (ha : a < 256 ^ l) :
    UInt8.ofNat ((a + b * 256 ^ l) / 256 ^ (l + j)) = UInt8.ofNat (b / 256 ^ j) := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem packed_append_bytes (l r a b : Nat) (ha : a < 256 ^ l) :
    (packed (l + r) (a + b * 256 ^ l)).bytes =
      (packed l a).bytes ++ (packed r b).bytes := by
  change List.ofFn _ = List.ofFn _ ++ List.ofFn _
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    exact packed_low a b l i.val i.isLt
  · congr 1
    funext j
    exact packed_high a b l j.val ha

theorem packed_appendSized_toByteArray (l r a b : Nat) (ha : a < 256 ^ l) :
    (appendSized l r (packed l a) (packed r b) rfl rfl).toByteArray =
      (packed (l + r) (a + b * 256 ^ l)).toByteArray := by
  unfold toByteArray appendSized
  rw [packed_append_bytes l r a b ha]

@[expose] def packedFast (width n : Nat) : KernelBytes where
  bytes := (packed width n).bytes
  size := width
  get i := if i < width then UInt8.ofNat (n >>> (8 * i)) else 0
  size_eq := (packed width n).size_eq
  get_eq i := by
    have hp : (2 : Nat) ^ (8 * i) = 256 ^ i := by
      rw [Nat.pow_mul]
    rw [Nat.shiftRight_eq_div_pow, hp]
    exact (packed width n).get_eq i

theorem packedFast_toByteArray (width n : Nat) :
    (packedFast width n).toByteArray = (packed width n).toByteArray := rfl

end CFSG.Sporadic.HNSchreier.KernelBytes
