module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.OrbRow.Defs

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow

@[expose] noncomputable def treeW (n w m idn : Nat) (G : List Nat) (k b : Nat) (R T : List Nat) :
    List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun j _ => Nat.beq j (lenS R))
    (fun t _ ih j seen => strictB (getS R j) (fun e =>
      strictB (Nat.land e m) (fun pt =>
      bAnd(Nat.beq (Nat.land seen (Nat.shiftLeft (nat_lit 1) pt)) (nat_lit 0),
      bAnd(bIf(Nat.beq j (nat_lit 0),
          bAnd(Nat.beq pt b, Nat.beq t idn),
          strictB (Nat.land (Nat.shiftRight e w) m) (fun par =>
          strictB (Nat.shiftRight e (Nat.add w w)) (fun g =>
            bAnd(Nat.blt par j, bAnd(Nat.blt g k, bAnd(Nat.beq (pg w m t b) pt,
              Nat.beq t (pcomp n w m (getS G g) (getS T par)))))))),
        strictB (Nat.succ j) (fun j' => ih j' (Nat.lor seen (Nat.shiftLeft (nat_lit 1) pt))))))))

@[expose] noncomputable def treeK (n w m idn : Nat) (G : List Nat) (b : Nat) (R T : List Nat) :
    Bool :=
  treeW n w m idn G (lenS G) b R T T (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def schW (n w m : Nat) (G : List Nat) (k b : Nat) (R T Ref Nn : List Nat) :
    List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun q => bAnd(Nat.beq q (lenS Ref), Nat.beq q (lenS Nn)))
    (fun s _ ih q => strictB (getS Ref q) (fun e =>
      strictB (Nat.land e m) (fun j =>
      strictB (Nat.shiftRight e w) (fun g =>
      strictB (getS Nn q) (fun j' =>
      bAnd(Nat.blt j (lenS R), bAnd(Nat.blt j' (lenS R), bAnd(Nat.blt g k,
      bAnd(canonK n w m (Nat.mul n w) s, bAnd(Nat.beq (pg w m s b) b,
      bAnd(Nat.beq (pcomp n w m (getS T j') s) (pcomp n w m (getS G g) (getS T j)),
        strictB (Nat.succ q) ih)))))))))))

@[expose] noncomputable def schK (n w m : Nat) (G : List Nat) (b : Nat) (R T Ref Nn S : List Nat) :
    Bool :=
  schW n w m G (lenS G) b R T Ref Nn S (nat_lit 0)

@[expose] noncomputable def commAllK (n w m : Nat) (G : List Nat) (t : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => bAnd(commK n w m (Nat.mul n w) g t, ih)) G

end CFSG.KC.HeChain

end
