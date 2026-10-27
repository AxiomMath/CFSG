module

public import Certificates.Data.Kernel.Sp62Pk

public section

namespace CFSG.KD.YamakiBicom

open CFSG.KD.Sp62 (MULF)

@[expose] noncomputable def bcComm (X g : Nat) : Bool := Nat.beq (MULF X g) (MULF g X)

@[expose] noncomputable def bcAll (X : Nat) (gs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun g _ r => Bool.and (bcComm X g) r) gs

@[expose] noncomputable def bcGL : List Nat :=
  [nat_lit 12430981749, nat_lit 19933438209, nat_lit 44307632885, nat_lit 21745569153,
    nat_lit 34790232227, nat_lit 34794427123, nat_lit 34628452488]

@[expose] noncomputable def bcG8 : Nat := nat_lit 35358961834

@[expose] noncomputable def bcB : List Nat :=
  [nat_lit 69222529, nat_lit 1049156, nat_lit 36864, nat_lit 67387528, nat_lit 151519234,
    nat_lit 9664724996, nat_lit 52, nat_lit 34359870720, nat_lit 536954880, nat_lit 13631488,
    nat_lit 34695282688, nat_lit 22011707392]

@[expose] def bcIdx : List (Fin 2 × (Fin 3 ⊕ Fin 3)) :=
  [(0, .inl 0), (0, .inl 1), (0, .inl 2), (0, .inr 0), (0, .inr 1), (0, .inr 2),
    (1, .inl 0), (1, .inl 1), (1, .inl 2), (1, .inr 0), (1, .inr 1), (1, .inr 2)]

@[expose] noncomputable def bcQ (gs : List Nat) (g8 X : Nat) : Bool :=
  Bool.or (Bool.not (bcAll X gs)) (bcComm X g8)

@[expose] noncomputable def bcChk (gs : List Nat) (g8 : Nat) (bs : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (bcQ gs g8)
    (fun b _ r acc => Bool.and (r acc) (r (Nat.xor acc b))) bs

end CFSG.KD.YamakiBicom
