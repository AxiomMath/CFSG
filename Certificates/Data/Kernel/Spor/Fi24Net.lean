module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.MonsterConv.PermValid

public section

namespace CFSG.KC.Fi24Net

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def ldist (l : Nat) : Nat :=
  Nat.shiftLeft (nat_lit 1) (nIf(Nat.blt l (nat_lit 19), l, Nat.sub (nat_lit 36) l))

@[expose] noncomputable def netF (M : Nat → Nat) (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun j ih x => strictN ((fun l => dsw (ldist l) (M l) x) (Nat.sub (nat_lit 36) j)) ih)
    (nat_lit 37) v

@[expose] noncomputable def netR (M : Nat → Nat) (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun j ih x => strictN ((fun l => dsw (ldist (Nat.sub (nat_lit 36) l)) (M (Nat.sub (nat_lit 36) l)) x)
      (Nat.sub (nat_lit 36) j)) ih)
    (nat_lit 37) v

@[expose] noncomputable def lidx (m : Nat) : Nat :=
  nIf(orB (Nat.beq m (nat_lit 1)) (Nat.beq m (nat_lit 3)), nat_lit 0,
    nIf(orB (Nat.ble m (nat_lit 2)) (Nat.beq m (nat_lit 4)), nat_lit 1, Nat.sub m (nat_lit 3)))

@[expose] noncomputable def appL (NW : Nat → Nat → Nat) (z : Int) (v : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun m => nIf(Nat.beq m (nat_lit 0), netR (NW (lidx m)) v, netF (NW (lidx m)) v))
    (fun n => nIf(Nat.beq n (nat_lit 0), netF (NW (nat_lit 0)) v, netR (NW (lidx (Nat.succ n))) v)) z

@[expose] noncomputable def walkW (NW : Nat → Nat → Nat) (w : List Int) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun z _ ih x => strictN (appL NW z x) ih) w v

@[expose] noncomputable def idPl (k : Nat) : Nat := idPlane (nat_lit 524288) k

@[expose] noncomputable def tpl (k : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), idPl (nat_lit 0), Nat.xor (idPl k) (idPl (nat_lit 0)))

@[expose] noncomputable def ptsM : Nat := ones (nat_lit 306936)

@[expose] noncomputable def padM : Nat := Nat.xor (ones (nat_lit 524288)) (ones (nat_lit 306936))

@[expose] noncomputable def masksOK (M : Nat → Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun l ih => andB ih (dswValid (nat_lit 524288) (ldist l) (M l))) (nat_lit 37)

@[expose] noncomputable def netOK (M : Nat → Nat) : Bool :=
  andB (masksOK M)
    (Nat.beq (netF M (Nat.xor ptsM (idPl (nat_lit 0)))) (Nat.xor ptsM (netF M (idPl (nat_lit 0)))))

@[expose] noncomputable def wordOK (NW : Nat → Nat → Nat) (w : List Int) (j k : Nat) : Bool :=
  letB (tpl k) (fun v => Nat.beq (walkW NW w v) (netF (NW j) v))

@[expose] noncomputable def blk (P c : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul c (nat_lit 512))) (ones (nat_lit 512))

@[expose] noncomputable def genBlk (OT : Nat → Nat) (b k Q c : Nat) : Nat :=
  Nat.lor
    (nIf(Nat.blt c (nat_lit 600),
      Nat.land (rawPlane (OT c) (nat_lit 64) (nat_lit 512) (nat_lit 9) (nat_lit 0) (Nat.add b k))
        (nIf(Nat.blt c (nat_lit 599), ones (nat_lit 512), ones (nat_lit 248))),
      nat_lit 0))
    (blk Q c)

@[expose] noncomputable def genOK (OT : Nat → Nat) (M : Nat → Nat) (b k : Nat) : Bool :=
  letB (netF M (tpl k)) (fun T =>
    letB (nIf(Nat.beq k (nat_lit 0), T, Nat.xor T (netF M (idPl (nat_lit 0))))) (fun P =>
      letB (Nat.land (idPl k) padM) (fun Q =>
        allBelow (nat_lit 1024) (nat_lit 16) (fun c => Nat.beq (blk P c) (genBlk OT b k Q c)))))

end CFSG.KC.Fi24Net

end
