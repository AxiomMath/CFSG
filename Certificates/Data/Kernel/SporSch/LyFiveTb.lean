module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.LyFiveTb

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def dig8 (x t : Nat) : Nat := fld(x, Nat.mul (nat_lit 3) t, nat_lit 7)

@[expose] noncomputable def enc8 (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun v _ acc => Nat.add v (Nat.mul (nat_lit 8) acc))
    l

@[expose] noncomputable def ent4 (m y t : Nat) : Nat :=
  (fun i j => Nat.mod (Nat.add (Nat.add (Nat.add
      (Nat.mul (dig8 m (Nat.mul (nat_lit 4) i)) (dig8 y j))
      (Nat.mul (dig8 m (Nat.add (Nat.mul (nat_lit 4) i) (nat_lit 1))) (dig8 y (Nat.add (nat_lit 4) j))))
      (Nat.mul (dig8 m (Nat.add (Nat.mul (nat_lit 4) i) (nat_lit 2))) (dig8 y (Nat.add (nat_lit 8) j))))
      (Nat.mul (dig8 m (Nat.add (Nat.mul (nat_lit 4) i) (nat_lit 3))) (dig8 y (Nat.add (nat_lit 12) j))))
      (nat_lit 5))
    (Nat.div t (nat_lit 4)) (Nat.mod t (nat_lit 4))

@[expose] noncomputable def ents4 (m y : Nat) : List Nat := (List.range 16).map (ent4 m y)

@[expose] noncomputable def mul4K (m y : Nat) : Nat := enc8 (ents4 m y)

@[expose] def id4K : Nat := 1 + 8 ^ 5 + 8 ^ 10 + 8 ^ 15

@[expose] noncomputable def key48 (T k : Nat) : Nat :=
  fld(T, Nat.mul (nat_lit 48) k, nat_lit 281474976710655)

@[expose] noncomputable def tbAt (G0 G1 PAR GEN KS k : Nat) : Bool :=
  bIf(Nat.beq k (nat_lit 0), Nat.beq (key48 KS k) id4K,
    bAnd(Nat.blt (pg (nat_lit 12) (mask (nat_lit 12)) PAR k) k,
      bAnd(Nat.blt (pg (nat_lit 12) (mask (nat_lit 12)) GEN k) (nat_lit 2),
        Nat.beq (key48 KS k)
          (mul4K (nIf(Nat.beq (pg (nat_lit 12) (mask (nat_lit 12)) GEN k) (nat_lit 1), G1, G0))
            (key48 KS (pg (nat_lit 12) (mask (nat_lit 12)) PAR k))))))

@[expose] noncomputable def tbOK (G0 G1 PAR GEN KS : Nat) : Bool :=
  allN (nat_lit 2880) (tbAt G0 G1 PAR GEN KS)

@[expose] noncomputable def sortAt (SK RHO KS i : Nat) : Bool :=
  bAnd(bIf(Nat.blt (Nat.succ i) (nat_lit 2880), Nat.blt (key48 SK i) (key48 SK (Nat.succ i)), true),
    bAnd(Nat.blt (pg (nat_lit 12) (mask (nat_lit 12)) RHO i) (nat_lit 2880),
      Nat.beq (key48 KS (pg (nat_lit 12) (mask (nat_lit 12)) RHO i)) (key48 SK i)))

@[expose] noncomputable def sortOK (SK RHO KS : Nat) : Bool :=
  allN (nat_lit 2880) (sortAt SK RHO KS)

end CFSG.KC.LyFiveTb

end
