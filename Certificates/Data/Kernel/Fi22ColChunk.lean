module

public import Certificates.Data.Kernel.Fi22Nbr3153

public section

namespace CFSG.KC.N3153

open CFSG.KC.Enum

@[expose] noncomputable def blkFold (n : Nat) (g : Nat → Nat → Nat → Nat) (s : Nat) : Nat :=
  (fun q => Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (g (Nat.shiftLeft h (nat_lit 6)) (nat_lit 64) s) ih)
      q (g (Nat.shiftLeft q (nat_lit 6)) (Nat.land n (nat_lit 63)) s))
    (Nat.shiftRight n (nat_lit 6))

@[expose] noncomputable def accBlkC (S : Nat → Nat) (b Ch len s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun l ih s => strictN (Nat.add s (Nat.mul (hcK (Nat.land (Nat.shiftRight Ch
      (Nat.mul (nat_lit 32) l)) (nat_lit 4294967295))) (S (Nat.add b l)))) ih) len s

@[expose] noncomputable def accKc (n : Nat) (S : Nat → Nat) (C M : Nat) : Nat :=
  blkFold n (fun b len s => strictN (Nat.land (Nat.shiftRight C
    (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) b))) M) fun Ch => accBlkC S b Ch len s) (nat_lit 0)

@[expose] noncomputable def newColC (T C Ch Ah b l : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mul (Nat.mod (Nat.add
    (Nat.mul (Nat.mod (Nat.land (Nat.shiftRight Ch (Nat.mul (nat_lit 32) l)) (nat_lit 4294967295))
      (nat_lit 2147483629)) (nat_lit 1000003))
    (Nat.mod (cget C (pg (nat_lit 12) (nat_lit 4095) T (Nat.add b l))) (nat_lit 2147483629)))
    (nat_lit 2147483629)) (nat_lit 1000003))
    (Nat.land (Nat.shiftRight Ah (Nat.mul (nat_lit 48) l)) (nat_lit 281474976710655)))
    (nat_lit 2147483629)

@[expose] noncomputable def stepBlkC (T C b Ch Ah len s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun l ih s => strictN (Nat.add (Nat.add s (Nat.shiftLeft (newColC T C Ch Ah b l)
      (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) l)))) (nat_lit 1)) ih) len s

@[expose] noncomputable def stepKc (n : Nat) (S : Nat → Nat) (T C : Nat) : Nat :=
  strictN (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)) (nat_lit 1)) fun M =>
  strictN (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 3072)) (nat_lit 1)) fun MA =>
  strictN (accKc n S C M) fun A =>
    blkFold n (fun b len s =>
      strictN (Nat.land (Nat.shiftRight C (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) b))) M) fun Ch =>
      strictN (Nat.land (Nat.shiftRight A (Nat.add (nat_lit 128) (Nat.mul (nat_lit 48) b))) MA)
        fun Ah => Nat.add (Nat.add s (Nat.shiftLeft (Nat.shiftRight
          (stepBlkC T C b Ch Ah len (Nat.mul (nat_lit 4096) (Nat.add b (nat_lit 1)))) (nat_lit 64))
          (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) b)))) len) (nat_lit 0)

@[expose] noncomputable def colourKc (n : Nat) (S : Nat → Nat) (T : Nat) (pre : List Nat)
    (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (initK n T pre)
    (fun _ C => strictN C fun C => stepKc n S T C) k

theorem rd_chunk (C o w f l : Nat) (h : f * l + f ≤ w) :
    ((C >>> o) &&& (2 ^ w - 1)) >>> (f * l) &&& (2 ^ f - 1) = (C >>> (o + f * l)) &&& (2 ^ f - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and,Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < f
  · have hw : f * l + i < w := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) h
    simp only [hw, hi, decide_true, Bool.and_true, Nat.add_assoc]
  · simp only [hi, decide_false, Bool.and_false]

end CFSG.KC.N3153

end
