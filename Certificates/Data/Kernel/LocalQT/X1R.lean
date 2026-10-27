module

public import Certificates.Data.Kernel.LocalQT.FusionS
public import Certificates.Data.Kernel.LocalQT.X1H

public section

namespace CFSG.KC.LQT.XR

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.BS CFSG.KC.LQT.RW CFSG.KC.LQT.RB
open CFSG.KC.LQT.FS CFSG.KC.LQT.XH

@[expose] noncomputable def pairsR (l : List Nat) : Option Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Option Nat → List (Nat × Nat)) (fun _ => [])
    (fun x _ ih pend => Option.rec (motive := fun _ => List (Nat × Nat)) (ih (some x))
      (fun y => List.cons (y, x) (ih none)) pend) l

@[expose] noncomputable def eqPL (l m : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun p _ ih m => List.rec (motive := fun _ => Bool) false
      (fun q m' _ => andB (andB (Nat.beq p.1 q.1) (Nat.beq p.2 q.2)) (ih m')) m) l m

@[expose] noncomputable def slp2H (n w : Nat) (ta tb : List Nat) (prog2 : List (Nat × Nat))
    (TF2 : Nat → Nat) (K m : Nat) : Bool :=
  allBs [tabL n ta, tabL n tb, slpOKK prog2 2, Nat.beq (TF2 0) (codeK w ta),
    Nat.beq (TF2 1) (codeK w tb), Nat.ble (Nat.add (lenA prog2) 2) (Nat.mul K m)]

@[expose] noncomputable def x1RA (n w : Nat) (ta tb : List Nat) (prog2 qp wprog : List (Nat × Nat))
    (TF2 : Nat → Nat) (K m : Nat) (TF3 : Nat → Nat) (K' m' : Nat) (gn gin hn hin an bn : Nat)
    (nodes1 nodes2 nodes3 : List Nat) : Bool :=
  (fun (N2 N3 : Nat) => (fun (g gi h hi : Nat) => allBs [slp2H n w ta tb prog2 TF2 K m,
      allA qp (fun p => andB (Nat.blt p.1 N2) (Nat.blt p.2 N2)),
      allA qp (fun p => Nat.beq (mulW n w (TF2 p.2) (TF2 p.1)) (oneW n w)),
      Nat.blt gn N2, Nat.blt gin N2, Nat.blt hn N2, Nat.blt hin N2,
      allL nodes1 (fun i => Nat.blt i N2), allL nodes2 (fun i => Nat.blt i N2),
      allL nodes3 (fun i => Nat.blt i N2),
      Nat.beq (mulW n w g gi) (oneW n w), Nat.beq (mulW n w gi g) (oneW n w),
      Nat.beq (mulW n w h hi) (oneW n w), Nat.beq (mulW n w hi h) (oneW n w),
      normK n w (mapW TF2 nodes1) g gi, normK n w (mapW TF2 nodes3) h hi,
      notNormK n w (mapW TF2 nodes3) g gi, notNormK n w (mapW TF2 nodes1) h hi,
      slpOKK wprog 2, Nat.beq (TF3 0) g, Nat.beq (TF3 1) h, Nat.ble N3 (Nat.mul K' m'),
      Nat.blt an N3, Nat.blt bn N3, Nat.beq (TF3 an) (codeK w ta), Nat.beq (TF3 bn) (codeK w tb)])
    (TF2 gn) (TF2 gin) (TF2 hn) (TF2 hin))
  (Nat.add (lenA prog2) 2) (Nat.add (lenA wprog) 2)

@[expose] noncomputable def rowK (w : Nat) (P : List Nat) (Y : Nat) : Nat :=
  codeK w (mapW (imgW w Y) P)

@[expose] noncomputable def passK (w nb : Nat) (G Z T : List Nat) : Bool :=
  allL (rangeK (lenA G)) fun j => anyL Z fun Y => allL (rangeK nb) fun k =>
    Nat.beq (getK T (Nat.add (Nat.mul nb (Nat.succ j)) k)) (imgW w Y (imgW w (getK G j) (getK T k)))

@[expose] noncomputable def eqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def claimK (w nb : Nat) (G Z LR : List Nat) (T : List Nat) (c : Nat) : Bool :=
  eqB (passK w nb G Z T) (anyL LR (Nat.beq c))

@[expose] noncomputable def zcS (n w : Nat) (B : List Nat) (qp : List (Nat × Nat)) (TF : Nat → Nat)
    (E BO : Nat → Nat) (M : Nat) (TF2 : Nat → Nat) (nodes1 nodes2 nodes3 : List Nat)
    (lo len : Nat) : Bool :=
  (fun (G : List Nat) => (fun (P : List Nat) =>
      (fun (Z1 Z2 Z3 : List Nat) =>
        (fun (R1 R2 R3 : List Nat) => allR lo len fun i => impB (Nat.blt i M)
            ((fun (c : Nat) => (fun (T : List Nat) => allBs [
                claimK w (lenA B) G [oneW n w] R1 T c, claimK w (lenA B) G Z1 R2 T c,
                claimK w (lenA B) G Z2 R3 T c])
              (decW w (lenA P) c)) (E (BO i))))
          (mapW (rowK w P) Z1) (mapW (rowK w P) Z2) (mapW (rowK w P) Z3))
        (mapW TF2 nodes1) (mapW TF2 nodes2) (mapW TF2 nodes3))
      (ptsW w B G))
    (fstT TF qp)

@[expose] noncomputable def zcH (w : Nat) (B : List Nat) (qp : List (Nat × Nat)) (TF : Nat → Nat)
    (M lg : Nat) (E : Nat → Nat) (N2 : Nat) (TF2 : Nat → Nat) (nodes1 nodes2 nodes3 : List Nat) :
    Bool :=
  (fun (P : List Nat) => allBs [
      allL nodes1 (fun i => Nat.blt i N2), allL nodes2 (fun i => Nat.blt i N2),
      allL nodes3 (fun i => Nat.blt i N2),
      allL nodes1 (fun i => memS w (lenA B) M lg E (rowK w P (TF2 i))),
      allL nodes2 (fun i => memS w (lenA B) M lg E (rowK w P (TF2 i))),
      allL nodes3 (fun i => memS w (lenA B) M lg E (rowK w P (TF2 i)))])
    (ptsW w B (fstT TF qp))

end CFSG.KC.LQT.XR

end
