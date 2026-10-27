module

public import Certificates.Data.Kernel.WeylE8.Roots
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def bindList (L : List Nat) (n P : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j n)
    (fun p _ ih j => bAnd(Nat.blt p (nat_lit 240),
      bAnd(Nat.beq p (pg (nat_lit 8) (nat_lit 255) P j), ih (Nat.succ j)))) L (nat_lit 0)

@[expose] noncomputable def witAt (PS : Nat → Nat) (T j : Nat) : Bool :=
  bAnd(Nat.blt j (nat_lit 120), Nat.beq T (PS j))

@[expose] noncomputable def negAt (RT : Nat → Nat) (T nr : Nat) : Bool :=
  bAnd(Nat.blt nr (nat_lit 240), Nat.beq (RT nr) T)

@[expose] noncomputable def reflFactAt (RT : Nat → Nat) (NEG WIT : Nat) (PS : Nat → Nat) (r T : Nat) :
    Bool :=
  bAnd(permOK (nat_lit 240) (nat_lit 8) (nat_lit 255) (nat_lit 1920) T T,
    bAnd(Nat.beq (fixCntK (nat_lit 240) (nat_lit 8) T) (nat_lit 126),
      bAnd(negAt RT T (pg (nat_lit 8) (nat_lit 255) NEG r),
        witAt PS T (pg (nat_lit 8) (nat_lit 255) WIT r))))

@[expose] noncomputable def reflFacts (RT : Nat → Nat) (NEG WIT : Nat) (PS : Nat → Nat) : Bool :=
  allN (nat_lit 240) fun r => strictB (RT r) fun T => reflFactAt RT NEG WIT PS r T

@[expose] noncomputable def negFacts (RT : Nat → Nat) (NEG : Nat) : Bool :=
  bAnd(permOK (nat_lit 240) (nat_lit 8) (nat_lit 255) (nat_lit 1920) NEG NEG,
  bAnd(Nat.beq (fixCntK (nat_lit 240) (nat_lit 8) NEG) (nat_lit 0),
    allN (nat_lit 240) fun r =>
      commK (nat_lit 240) (nat_lit 8) (nat_lit 255) (nat_lit 1920) NEG (RT r)))

end CFSG.KLC.E8

end
