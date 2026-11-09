module

public import Certificates.Kernel.Co1P.Defs

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1P

@[expose] noncomputable def bitsZ (h m w : Nat) : List (Nat × Nat) :=
  Bool.rec (motive := fun _ => List (Nat × Nat)) (bitsK h m w (nat_lit 0)) List.nil
    (Nat.beq m (nat_lit 0))

@[expose] noncomputable def recsFromZ (w : Nat) (ms : List Nat) : Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => List.nil)
    (fun m _ ih h => List.append (bitsZ h m w)
      (Nat.rec (motive := fun _ => List (Nat × Nat)) (ih (nat_lit 0)) (fun n _ => ih (Nat.succ n))
        (Nat.succ h))) ms

@[expose] noncomputable def recsZ (ms : List Nat) : List (Nat × Nat) :=
  recsFromZ 8 (masksK 8 64 ms) (nat_lit 0)

theorem bitsK_zero (h k l : Nat) : bitsK h 0 k l = [] := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    change Bool.rec (motive := fun _ => List (Nat × Nat)) (bitsK h 0 k (l + 1))
      ((h, l) :: bitsK h 0 k (l + 1)) (Nat.beq (Nat.land (Nat.shiftRight 0 l) 1) 1) = []
    have hz : Nat.shiftRight 0 l = 0 := Nat.zero_shiftRight l
    rw [hz, ih]
    rfl

theorem bitsZ_eq (h m w : Nat) : bitsZ h m w = bitsK h m w 0 := by
  unfold bitsZ
  cases hm : Nat.beq m 0 with
  | false => rfl
  | true =>
    rw [Nat.eq_of_beq_eq_true hm, bitsK_zero]

theorem recsFromZ_eq (w : Nat) (ms : List Nat) (h : Nat) : recsFromZ w ms h = recsFrom w ms h := by
  induction ms generalizing h with
  | nil => rfl
  | cons m ms ih =>
    change List.append (bitsZ h m w) (recsFromZ w ms (h + 1)) =
      List.append (bitsK h m w 0) (recsFrom w ms (h + 1))
    rw [bitsZ_eq, ih]

theorem recsT_eq_recsZ (ms : List Nat) : recsT ms = recsZ ms :=
  (recsFromZ_eq 8 (masksK 8 64 ms) 0).symm

end CertificateChecks.KernelCo1P

end
