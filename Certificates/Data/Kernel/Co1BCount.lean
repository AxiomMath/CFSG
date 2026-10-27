module

public import Certificates.Data.Kernel.Co1BW

public section

namespace CFSG.KC.Co1B

open CFSG.KC.Loop

@[expose] noncomputable def code4 (A O W V S : Nat) : Nat :=
  Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (eqK S A))
    (Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 512) (eqK S O))
      (Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 262144) (eqK S W))
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 134217728) (eqK S V))))

@[expose] noncomputable def sqCode (A O W V X : Nat) : Nat :=
  strictN X fun X => strictN (mulWK X X) (code4 A O W V)

@[expose] noncomputable def cnt4 (A O W V H : Nat) (YP : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun Y _ ih => Nat.add (sqCode A O W V (mulWK H Y))
      (Nat.add (sqCode A O W V (mulWK H (mulWK Y A))) ih)) YP

end CFSG.KC.Co1B

end
