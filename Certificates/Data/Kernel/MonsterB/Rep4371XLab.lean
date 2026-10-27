module

public import Certificates.Data.Kernel.MonsterB.Rep4371XNf

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Rep4371Row CFSG.KC.BM.B64

@[expose] noncomputable def hexD (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 58), Nat.sub c (nat_lit 48), Nat.sub c (nat_lit 55))

@[expose] noncomputable def hexT (N o w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => Nat.add (Nat.mul ih (nat_lit 16)) (hexD (chAt N (Nat.add o k)))) w

@[expose] noncomputable def ascChk (N len hi : Nat) : Bool :=
  allBelow len hi fun k => Nat.blt (chAt N k) (nat_lit 128)

@[expose] noncomputable def labT (N t c c' : Nat) : Bool :=
  (fun o => bAnd(Nat.beq (kt c) (nat_lit 1), bAnd(Nat.beq (kt c') (nat_lit 1),
    bAnd(Nat.beq (hexT N o (nat_lit 1)) (nat_lit 0),
    bAnd(Nat.beq (hexT N (Nat.add o (nat_lit 1)) (nat_lit 3)) (kx c),
    bAnd(Nat.beq (hexT N (Nat.add o (nat_lit 4)) (nat_lit 3)) (ky c),
    bAnd(Nat.beq (hexT N (Nat.add o (nat_lit 7)) (nat_lit 1)) (nat_lit 0),
    bAnd(Nat.beq (hexT N (Nat.add o (nat_lit 8)) (nat_lit 3)) (kx c'),
      Nat.beq (hexT N (Nat.add o (nat_lit 11)) (nat_lit 3)) (ky c')))))))))
    (Nat.mul (nat_lit 14) t)

@[expose] noncomputable def lab2 (N t : Nat) (L : Terms) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun e r _ => List.rec (motive := fun _ => Bool) false
      (fun e' r' _ => bAnd(nilB r', labT N t e.1 e'.1)) r) L

@[expose] noncomputable def labChk (TH N : Nat) : Bool :=
  allBelow (nat_lit 2300) (nat_lit 36) fun t => lab2 N t (rawT TH (Nat.add (nat_lit 23) t))

@[expose] noncomputable def spinChk (N o : Nat) : Bool :=
  allBelow (nat_lit 2048) (nat_lit 32) fun t =>
    Nat.beq (hexT N (Nat.add o (Nat.mul (nat_lit 3) t)) (nat_lit 3))
      (Nat.add (nIf(Nat.ble (nat_lit 1024) t, nat_lit 2048, nat_lit 0))
        (Nat.div (oddT (Nat.mod t (nat_lit 1024))) (nat_lit 2)))

@[expose] noncomputable def textN (CH : List (Nat × Nat)) : Nat := (CFSG.KC.BM.Pkt.joinP CH (nat_lit 0) (nat_lit 151)).1

@[expose] noncomputable def labText (TH : Nat) (T : Nat × Nat) : Bool :=
  bAnd(Nat.beq T.2 (nat_lit 38346), bAnd(ascChk T.1 (nat_lit 38346) (nat_lit 600),
    bAnd(labChk TH T.1, spinChk T.1 (nat_lit 32201))))

end CFSG.KC.Rep4371X

end
