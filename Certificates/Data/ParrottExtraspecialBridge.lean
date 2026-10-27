module

public import Certificates.Data.ParrottExtraspecial

public section

open scoped BigOperators Matrix

namespace CFSG.RankThree.GF2n.Parrott

theorem bitmask_lt_256 (v : V) : bitmask v < 256 := by
  have hterm : ∀ i : Fin 8, (v i).val <<< (i : Nat) ≤ 1 <<< (i : Nat) := by
    intro i
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have hv := ZMod.val_lt (v i)
    exact Nat.mul_le_mul_right _ (by omega)
  have h : bitmask v ≤ ∑ i : Fin 8, (1 <<< (i : Nat)) :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have hsum : (∑ i : Fin 8, (1 <<< (i : Nat))) = 255 := by
    norm_num [Fin.sum_univ_eight, Nat.one_shiftLeft]
  omega

@[expose] def e8Mask (e : E8) : Nat :=
  bitmask (packE8 e) + (e.a.val <<< 8)

theorem e8Mask_lt_512 (e : E8) : e8Mask e < 512 := by
  unfold e8Mask
  have hb : bitmask (packE8 e) < 256 := bitmask_lt_256 _
  have ha := ZMod.val_lt e.a
  have hle : e.a.val ≤ 1 := by omega
  have hs : e.a.val <<< 8 ≤ 256 := by
    rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 from by norm_num]
    exact Nat.mul_le_mul_right _ hle
  omega

theorem e8Mask_mod_256 (e : E8) : e8Mask e % 256 = bitmask (packE8 e) := by
  unfold e8Mask
  rw [Nat.add_comm, Nat.shiftLeft_eq]
  have hb : bitmask (packE8 e) < 2 ^ 8 := by simpa using bitmask_lt_256 (packE8 e)
  rw [show (2 : Nat) ^ 8 = 256 from by norm_num]
  rw [Nat.mul_add_mod_of_lt (by simpa using hb)]

theorem e8Mask_shiftRight_8 (e : E8) : (e8Mask e >>> 8) % 2 = e.a.val := by
  unfold e8Mask
  rw [Nat.add_comm, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hb : bitmask (packE8 e) < 2 ^ 8 := by simpa using bitmask_lt_256 (packE8 e)
  rw [Nat.mul_comm e.a.val (2 ^ 8), Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hb,
    Nat.add_zero]
  exact Nat.mod_eq_of_lt (ZMod.val_lt e.a)

theorem e8Mask_injective : Function.Injective e8Mask := by
  intro e f h
  have hlow : bitmask (packE8 e) = bitmask (packE8 f) := by
    have hh := congrArg (fun n => n % 256) h
    simpa [e8Mask_mod_256] using hh
  have hpack : packE8 e = packE8 f := bitmask_injective hlow
  have hx : e.x = f.x := by
    funext i
    rw [← packE8_x e i, ← packE8_x f i, hpack]
  have hy : e.y = f.y := by
    funext i
    rw [← packE8_y e i, ← packE8_y f i, hpack]
  have ha : e.a = f.a := by
    apply ZMod.val_injective 2
    have hh := congrArg (fun n => (n >>> 8) % 2) h
    simpa [e8Mask_shiftRight_8] using hh
  exact E8.ext hx hy ha

end CFSG.RankThree.GF2n.Parrott
