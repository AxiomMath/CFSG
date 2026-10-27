module

public import Certificates.Data.Kernel.Co2InvS

public section

namespace CFSG.KC.Co2Smith

open CFSG.KC.Co2InvS

@[expose] noncomputable def wK (P : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) IDP (fun k _ acc => mulV (P k) acc) w

@[expose] noncomputable def powK (A : Nat) (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) IDP (fun _ acc => mulV acc A) e

@[expose] noncomputable def cK (A : Nat) : Nat := Nat.mod A (nat_lit 49947976805055875702105555676690660891977570282639538413746511354005947821116249921924897649015871538557230897942505966327167610868612564900642816)

@[expose] noncomputable def eqK (A B : Nat) : Bool := Nat.beq (cK A) (cK B)

@[expose] noncomputable def commK (A B : Nat) : Bool := eqK (mulV A B) (mulV B A)

end CFSG.KC.Co2Smith
