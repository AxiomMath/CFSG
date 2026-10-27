module

public import CFSG.Certificates.Kernel.Local.HN.X.Lib
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Local.HN.Lib
public import CFSG.Certificates.Kernel.Local.LargeCore.Grp2

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX

@[expose] noncomputable def hnxC (b : Nat) : Nat := nIf(Nat.blt b (nat_lit 17812), nat_lit 64, nat_lit 32)

@[expose] noncomputable def hnxS (m : Nat) : Nat := nIf(Nat.blt m (nat_lit 17812), nat_lit 64, nat_lit 31)

@[expose] noncomputable def sumK (CNT : Nat → Nat) : Nat :=
  foldN (nat_lit 17813) (fun b acc => Nat.add acc (CNT b)) (nat_lit 0)

@[expose] noncomputable def linkK (SGT : Nat → Nat) : Bool :=
  allN (nat_lit 17812) (fun m =>
    Nat.beq (fldW (SGT m) (nat_lit 1344) (nat_lit 21)) (fldW (SGT (Nat.succ m)) (nat_lit 0) (nat_lit 21)))

@[expose] noncomputable def rootRun (V : Nat) (cs : List Char) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun k => bAnd(Nat.beq k (nat_lit 133), Nat.blt V (Nat.shiftLeft (nat_lit 1) (nat_lit 399))))
    (fun ch _ ih k => strictB (Char.toNat ch) (fun c =>
      bAnd(Nat.ble (nat_lit 48) c, bAnd(Nat.ble c (nat_lit 52),
      bAnd(Nat.beq (Nat.sub c (nat_lit 48)) (fldW V (Nat.mul (nat_lit 3) k) (nat_lit 3)),
        strictB (Nat.succ k) ih))))) cs

@[expose] noncomputable def rootK (V : Nat) (cs : List Char) : Bool := rootRun V cs (nat_lit 0)

@[expose] noncomputable def wsKX (c : Nat) : Bool :=
  bIf(Nat.beq c (nat_lit 32), true, bAnd(Nat.ble (nat_lit 9) c, Nat.ble c (nat_lit 13)))

@[expose] noncomputable def dig5KX (c : Nat) : Nat :=
  nIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)), Nat.mod (Nat.sub c (nat_lit 48)) (nat_lit 5),
    nat_lit 0)

@[expose] noncomputable def seedRun (W : Nat) (cs : List Char) : Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun ph i _ _ => bAnd(Nat.beq ph (nat_lit 1), Nat.beq i (nat_lit 133)))
    (fun ch _ ih ph i j acc => strictB (Char.toNat ch) (fun c =>
      bIf(Nat.beq ph (nat_lit 0),
        bIf(Nat.beq c (nat_lit 10), ih (nat_lit 1) i j acc, ih ph i j acc),
      bIf(wsKX c, ih ph i j acc,
      bIf(Nat.beq i (nat_lit 133), ih ph i j acc,
        strictB (Nat.lor acc (Nat.shiftLeft (dig5KX c) (Nat.mul (nat_lit 13) j))) (fun a =>
          bIf(Nat.beq j (nat_lit 132),
            bAnd(Nat.beq (fldW W (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) a,
              strictB (Nat.succ i) (fun i' => ih ph i' (nat_lit 0) (nat_lit 0))),
            strictB (Nat.succ j) (fun j' => ih ph i j' a)))))))) cs

@[expose] noncomputable def seedRK (W : Nat) (cs : List Char) : Bool :=
  seedRun W cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def qBlk (T : Nat → Nat) (Q : List Nat) (t : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun q _ ih k => strictN (ih (Nat.succ k)) (fun rest =>
      nIf(Nat.beq (Nat.shiftRight k (nat_lit 6)) t,
        Nat.lor rest (Nat.shiftLeft (fldW (getRec T (nat_lit 464) q) (nat_lit 0) (nat_lit 399))
          (Nat.mul (nat_lit 1729) (Nat.land k (nat_lit 63)))), rest))) Q (nat_lit 0)

@[expose] noncomputable def idBlk (t c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul (nat_lit 1729) r)
      (Nat.mul (nat_lit 13) (Nat.add (Nat.mul (nat_lit 64) t) r))))) c

@[expose] noncomputable def lenQ (Q : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) Q

@[expose] noncomputable def allQ (Q : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun q _ ih => bAnd(Nat.blt q (nat_lit 1140000), ih)) Q

@[expose] noncomputable def canonG (G : Nat) : Bool :=
  bAnd(Nat.blt G (Nat.shiftLeft (nat_lit 1) (nat_lit 229957)),
    allN (nat_lit 133) (fun i => strictB (fldW G (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) (fun r =>
      allN (nat_lit 133) (fun j => Nat.blt (fldW r (Nat.mul (nat_lit 13) j) (nat_lit 13)) (nat_lit 5)))))

@[expose] noncomputable def qBasisK (T : Nat → Nat) (CM3 : Nat) (Q : List Nat) (G : Nat) : Bool :=
  bAnd(Nat.beq (lenQ Q) (nat_lit 133), bAnd(allQ Q, bAnd(canonG G,
    bAnd(Nat.beq (mulC CM3 (qBlk T Q (nat_lit 0)) G) (idBlk (nat_lit 0) (nat_lit 64)),
    bAnd(Nat.beq (mulC CM3 (qBlk T Q (nat_lit 1)) G) (idBlk (nat_lit 1) (nat_lit 64)),
      Nat.beq (mulC CM3 (qBlk T Q (nat_lit 2)) G) (idBlk (nat_lit 2) (nat_lit 5)))))))

end CFSG.KS.SporSch

end
