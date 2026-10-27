module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.ONK3

open CFSG.KC.Enum

@[expose] noncomputable def M18 : Nat := nat_lit 262143

@[expose] noncomputable def M54 : Nat := nat_lit 18014398509481983

@[expose] noncomputable def M42 : Nat := nat_lit 4398046511103

@[expose] noncomputable def M72 : Nat := nat_lit 4722366482869645213695

@[expose] noncomputable def M193 : Nat :=
  nat_lit 12554203470773361527671578846415332832204710888928069025791

@[expose] noncomputable def CNT : Nat := nat_lit 161280

@[expose] noncomputable def NP : Nat := nat_lit 245520

@[expose] noncomputable def BK : Nat := nat_lit 6928151191748608

@[expose] noncomputable def nrec (R : Nat → Nat) (k : Nat) : Nat :=
  rget R (nat_lit 6) (nat_lit 63) (nat_lit 193) M193 k

@[expose] noncomputable def tA (r : Nat) : Nat := fld(r, nat_lit 0, M18)
@[expose] noncomputable def tB (r : Nat) : Nat := fld(r, nat_lit 18, M18)
@[expose] noncomputable def tC (r : Nat) : Nat := fld(r, nat_lit 36, M18)
@[expose] noncomputable def tK (r : Nat) : Nat := fld(r, nat_lit 0, M54)
@[expose] noncomputable def posF (r j : Nat) : Nat := fld(r, Nat.add (nat_lit 54) (Nat.mul (nat_lit 18) j), M18)
@[expose] noncomputable def parF (r : Nat) : Nat := fld(r, nat_lit 108, M18)
@[expose] noncomputable def labF (r : Nat) : Nat := fld(r, nat_lit 126, nat_lit 3)
@[expose] noncomputable def sigF (r : Nat) : Nat := fld(r, nat_lit 128, M18)
@[expose] noncomputable def depF (r : Nat) : Nat := fld(r, nat_lit 146, nat_lit 31)
@[expose] noncomputable def wrdF (r : Nat) : Nat := fld(r, nat_lit 151, M42)

@[expose] noncomputable def walk (R : Nat → Nat) (d : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ j => j)
    (fun _ ih w j => strictN (posF (nrec R j) (Nat.land w (nat_lit 3))) fun j' =>
      ih (Nat.shiftRight w (nat_lit 2)) j') d

@[expose] noncomputable def lexB (a b c d : Nat) : Bool :=
  bIf(Nat.blt a c, true, bAnd(Nat.beq a c, Nat.blt b d))

@[expose] noncomputable def closeOK (G : Nat → Nat → Nat) (R : Nat → Nat) (k r j : Nat) : Bool :=
  strictB (posF r j) fun p => strictB (nrec R p) fun rp =>
    bAnd(Nat.blt p CNT, bAnd(Nat.beq (G j (tA r)) (tA rp), bAnd(Nat.beq (G j (tB r)) (tB rp),
    bAnd(Nat.beq (G j (tC r)) (tC rp),
      bIf(Nat.beq p (nat_lit 0), true, bIf(Nat.blt (parF rp) k, true,
        bAnd(Nat.beq (parF rp) k, Nat.ble (labF rp) j)))))))

@[expose] noncomputable def treeAt (R : Nat → Nat) (UL UW : Nat → Nat) (k r : Nat) : Bool :=
  bIf(Nat.beq k (nat_lit 0),
    bAnd(Nat.beq (tK r) BK, bAnd(Nat.beq (parF r) (nat_lit 0), bAnd(Nat.beq (labF r) (nat_lit 0),
    bAnd(Nat.beq (sigF r) (nat_lit 0), bAnd(Nat.beq (depF r) (nat_lit 0),
      Nat.beq (wrdF r) (nat_lit 0)))))),
    strictB (parF r) fun q => strictB (labF r) fun l => strictB (nrec R q) fun rq =>
      bAnd(Nat.blt q k, bAnd(Nat.blt l (nat_lit 3), bAnd(Nat.beq (posF rq l) k,
      bAnd(Nat.beq (depF r) (Nat.succ (depF rq)),
      bAnd(Nat.beq (wrdF r) (Nat.add (wrdF rq) (Nat.shiftLeft l (Nat.mul (nat_lit 2) (depF rq)))),
        Nat.beq (sigF r) (walk R (UL l) (UW l) (sigF rq))))))))

@[expose] noncomputable def orderAt (R : Nat → Nat) (k r : Nat) : Bool :=
  bIf(Nat.beq k (nat_lit 0), true,
    bIf(Nat.blt (Nat.succ k) CNT, strictB (nrec R (Nat.succ k)) fun r' =>
      lexB (parF r) (labF r) (parF r') (labF r'), true))

@[expose] noncomputable def memK (L n x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun i ih => bIf(Nat.beq (fld(L, Nat.mul (nat_lit 54) i, M54)) x, true, ih)) n

@[expose] noncomputable def nodeOK (G : Nat → Nat → Nat) (R : Nat → Nat) (UL UW : Nat → Nat)
    (FK : Nat) (k : Nat) : Bool :=
  strictB (nrec R k) fun r =>
    bAnd(Nat.blt (tA r) NP, bAnd(Nat.blt (tB r) NP, bAnd(Nat.blt (tC r) NP,
    bAnd(closeOK G R k r (nat_lit 0), bAnd(closeOK G R k r (nat_lit 1),
    bAnd(closeOK G R k r (nat_lit 2), bAnd(treeAt R UL UW k r, bAnd(orderAt R k r,
      bIf(Nat.beq (sigF r) k, memK FK (nat_lit 120) (tK r), true)))))))))

@[expose] noncomputable def tVal (R : Nat → Nat) (k : Nat) : Nat :=
  strictN (nrec R k) fun r =>
    nIf(Nat.beq (walk R (depF r) (wrdF r) (sigF r)) (nat_lit 0), nat_lit 1, nat_lit 0)

@[expose] noncomputable def sumBlk (b : Nat) (f : Nat → Nat) (len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun l ih => Nat.add (f (Nat.add b l)) ih) len

@[expose] noncomputable def sliceOK (G : Nat → Nat → Nat) (R : Nat → Nat) (UL UW : Nat → Nat)
    (FK : Nat) (TC : Nat → Nat) (s : Nat) : Bool :=
  bAnd(allBlk (Nat.mul s (nat_lit 512)) (nodeOK G R UL UW FK) (nat_lit 512),
    Nat.beq (sumBlk (Nat.mul s (nat_lit 512)) (tVal R) (nat_lit 512)) (TC s))

@[expose] noncomputable def srec (SR : Nat → Nat) (i : Nat) : Nat :=
  rget SR (nat_lit 6) (nat_lit 63) (nat_lit 72) M72 i

@[expose] noncomputable def sortOK (R SR : Nat → Nat) (i : Nat) : Bool :=
  strictB (srec SR i) fun s => strictB (fld(s, nat_lit 54, M18)) fun x =>
    bAnd(Nat.blt x CNT, bAnd(Nat.beq (fld(s, nat_lit 0, M54)) (tK (nrec R x)),
      bIf(Nat.blt (Nat.succ i) CNT,
        Nat.blt (fld(s, nat_lit 0, M54)) (fld(srec SR (Nat.succ i), nat_lit 0, M54)), true)))

@[expose] noncomputable def sortSl (R SR : Nat → Nat) (s : Nat) : Bool :=
  allBlk (Nat.mul s (nat_lit 2520)) (sortOK R SR) (nat_lit 2520)

end CFSG.KC.ONK3

end
