module

public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KS.SporSch.PF2

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def repU (s k : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul s k)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) s) (nat_lit 1))

@[expose] noncomputable def mstepP (d c rm A B acc k : Nat) : Nat :=
  Nat.xor acc (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) c) rm)
    (Nat.mul (Nat.land (Nat.shiftRight B (Nat.mul d k)) rm) c))

@[expose] noncomputable def mulP (d A B : Nat) : Nat :=
  strictN (repU d d) fun c => strictN (Nat.sub (pw2 d) (nat_lit 1)) fun rm =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => mstepP d c rm A B acc k) d

@[expose] noncomputable def spreadP (E O ME MO r i : Nat) : Nat :=
  Nat.shiftLeft (Nat.lor (Nat.land (Nat.mul r E) ME) (Nat.land (Nat.mul r O) MO)) i

@[expose] noncomputable def trP (d A : Nat) : Nat :=
  strictN (repU (Nat.mul (nat_lit 2) (Nat.sub d (nat_lit 1))) (Nat.div (Nat.succ d) (nat_lit 2)))
    fun E => strictN (Nat.shiftLeft (repU (Nat.mul (nat_lit 2) (Nat.sub d (nat_lit 1)))
      (Nat.div d (nat_lit 2))) (Nat.sub d (nat_lit 1))) fun O =>
    strictN (repU (Nat.mul (nat_lit 2) d) (Nat.div (Nat.succ d) (nat_lit 2))) fun ME =>
    strictN (Nat.shiftLeft (repU (Nat.mul (nat_lit 2) d) (Nat.div d (nat_lit 2))) d) fun MO =>
      orN d fun i => spreadP E O ME MO (rowF d A i) i

@[expose] noncomputable def offP (d i : Nat) : Nat :=
  Nat.sub (Nat.mul d i) (Nat.div (Nat.mul i (Nat.sub i (nat_lit 1))) (nat_lit 2))

@[expose] noncomputable def triP (d z : Nat) : Nat :=
  orN d fun i => Nat.shiftLeft (Nat.land (Nat.shiftRight z (offP d i))
    (Nat.sub (pw2 (Nat.sub d i)) (nat_lit 1))) (Nat.add i (Nat.mul d i))

@[expose] noncomputable def diagP (d : Nat) : Nat := repU (Nat.succ d) d

@[expose] noncomputable def canonP (d C : Nat) : Nat :=
  strictN (diagP d) fun D =>
  strictN (Nat.sub (Nat.shiftLeft (repU d d) d) (Nat.mul (nat_lit 2) D)) fun SU =>
    Nat.lor (Nat.land (Nat.xor C (trP d C)) SU) (Nat.land C D)

@[expose] noncomputable def pullK (d A AT z z' : Nat) : Bool :=
  Nat.beq (canonP d (mulP d AT (mulP d (triP d z') A))) (triP d z)

end CFSG.KS.SporSch.PF2

end
