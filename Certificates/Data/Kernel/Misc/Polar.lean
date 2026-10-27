module

public import Certificates.Data.Kernel.Misc.T46

public section

namespace CFSG.KC.Misc.Polar

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46

@[expose] noncomputable def hermR (c d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.xor acc
    (f4K (crdK c i) (f4K (crdK d i) (crdK d i)))) 6

@[expose] noncomputable def nontrivK (UP : Nat) : Bool :=
  allN 693 fun p => letB (at' 12 UP p) fun P =>
    anyN 693 fun x => notB (Nat.beq (hermR (at' 12 UP x) P) 0)

@[expose] noncomputable def sepK (UP lo n : Nat) : Bool :=
  allN n fun d => letB (Nat.add lo d) fun p => impB (Nat.blt p 693) <|
    letB (at' 12 UP p) fun P => allN 693 fun q => impB (Nat.blt p q) <|
      letB (at' 12 UP q) fun Q => anyN 693 fun x => letB (at' 12 UP x) fun X =>
        letB (hermR X P) fun a => letB (hermR X Q) fun b =>
          orB (andB (Nat.beq a 0) (notB (Nat.beq b 0))) (andB (Nat.beq b 0) (notB (Nat.beq a 0)))

end CFSG.KC.Misc.Polar

end
