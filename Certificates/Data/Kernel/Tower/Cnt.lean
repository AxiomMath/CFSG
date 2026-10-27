module

public import Certificates.Data.Kernel.Tower.Cls14
public import Certificates.Data.Kernel.Tower.Chunk

public section

namespace Certificates.KernelTower

@[expose] noncomputable def hmL (HL m : Nat) : Nat :=
  Nat.rec 0 (fun j acc => Nat.lor acc (Nat.shiftLeft 1 (l16 HL j))) m

@[expose] noncomputable def pcR (n : Nat) (mul : Nat → Nat → Nat) (OT LB RP CZ nl t x0 : Nat) : Bool :=
  allB nl fun l => Nat.beq l (lbL LB t) || Nat.beq l (lbL LB x0) ||
    !(Nat.beq (oe OT (l16 RP l)) 1 && Nat.beq (lane CZ 15 32767 l) 64 &&
        Nat.beq (ninvC n mul OT (l16 RP l)) 87)

@[expose] noncomputable def czHB (H CZ nl : Nat) : Bool :=
  allB nl fun l => Nat.beq (lane H 15 32767 l) (lane CZ 14 16383 l)

theorem pcR_pcB {n : Nat} {mul : Nat → Nat → Nat} {OT LB RP CZ nl t x0 : Nat}
    (h : pcR n mul OT LB RP CZ nl t x0 = true) : pcB n mul OT LB RP CZ nl t x0 = true := by
  rw [pcR, allB_true_iff] at h
  rw [pcB, allB_true_iff]
  intro l hl
  have h1 := h l hl
  revert h1
  cases Nat.beq l (lbL LB t) <;> cases Nat.beq l (lbL LB x0) <;> simp

end Certificates.KernelTower
