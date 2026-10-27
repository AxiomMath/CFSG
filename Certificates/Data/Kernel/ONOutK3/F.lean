module

public import Certificates.Data.Kernel.ONOutK3.Check

public section

namespace CFSG.KC.ONK3

open CFSG.KC.Enum

@[expose] noncomputable def M73 : Nat := nat_lit 9444732965739290427391

@[expose] noncomputable def M6 : Nat := nat_lit 63

@[expose] noncomputable def gword (G : Nat → Nat → Nat) (d : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih w x => strictN (G (Nat.land w (nat_lit 3)) x) fun x' =>
      ih (Nat.shiftRight w (nat_lit 2)) x') d

@[expose] noncomputable def evalWK (G : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.foldr (fun a q => G a q) x w

@[expose] noncomputable def FW (l : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) [1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2]
    [1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 0] (Nat.beq l (nat_lit 0))

@[expose] noncomputable def fG (G : Nat → Nat → Nat) (l x : Nat) : Nat := evalWK G (FW l) x

@[expose] noncomputable def key3 (a b c : Nat) : Nat :=
  Nat.add a (Nat.add (Nat.mul b (nat_lit 262144)) (Nat.mul c (nat_lit 68719476736)))

@[expose] noncomputable def mapK (g : Nat → Nat) (t : Nat) : Nat :=
  key3 (g (tA t)) (g (tB t)) (g (tC t))

@[expose] noncomputable def fRec (FL j : Nat) : Nat := fld(FL, Nat.mul (nat_lit 73) j, M73)

@[expose] noncomputable def fPos (r l : Nat) : Nat := fld(r, Nat.add (nat_lit 54) (Nat.mul (nat_lit 6) l), M6)
@[expose] noncomputable def fPar (r : Nat) : Nat := fld(r, nat_lit 66, M6)
@[expose] noncomputable def fLab (r : Nat) : Nat := fld(r, nat_lit 72, nat_lit 1)

@[expose] noncomputable def fClose (G : Nat → Nat → Nat) (FL j r l : Nat) : Bool :=
  strictB (fPos r l) fun p => strictB (fRec FL p) fun rp =>
    bAnd(Nat.blt p (nat_lit 60), bAnd(Nat.beq (mapK (fG G l) r) (tK rp),
      bIf(Nat.beq p (nat_lit 0), true, bIf(Nat.blt (fPar rp) j, true,
        bAnd(Nat.beq (fPar rp) j, Nat.ble (fLab rp) l)))))

@[expose] noncomputable def fNode (G : Nat → Nat → Nat) (FL FK j : Nat) : Bool :=
  strictB (fRec FL j) fun r =>
    bAnd(Nat.blt (tA r) NP, bAnd(Nat.blt (tB r) NP, bAnd(Nat.blt (tC r) NP,
    bAnd(fClose G FL j r (nat_lit 0), bAnd(fClose G FL j r (nat_lit 1),
    bAnd(bIf(Nat.beq j (nat_lit 0),
        bAnd(Nat.beq (tK r) BK, bAnd(Nat.beq (fPar r) (nat_lit 0), Nat.beq (fLab r) (nat_lit 0))),
        strictB (fPar r) fun q => strictB (fLab r) fun l =>
          bAnd(Nat.blt q j, bAnd(Nat.blt l (nat_lit 2), Nat.beq (fPos (fRec FL q) l) j))),
    bAnd(bIf(Nat.beq j (nat_lit 0), true, bIf(Nat.blt (Nat.succ j) (nat_lit 60),
        strictB (fRec FL (Nat.succ j)) fun r' => lexB (fPar r) (fLab r) (fPar r') (fLab r'), true)),
    bAnd(allN j (fun i => bIf(Nat.beq (tK (fRec FL i)) (tK r), false, true)),
    bAnd(Nat.beq (fld(FK, Nat.mul (nat_lit 54) j, M54)) (tK r),
    bAnd(Nat.beq (fld(FK, Nat.mul (nat_lit 54) (Nat.add (nat_lit 60) j), M54)) (mapK (G (nat_lit 0)) r),
      bIf(Nat.beq (tK r) (mapK (G (nat_lit 0)) BK), false, true)))))))))))

@[expose] noncomputable def fAll (G : Nat → Nat → Nat) (FL FK : Nat) : Bool :=
  allN (nat_lit 60) (fNode G FL FK)

@[expose] noncomputable def uG (G : Nat → Nat → Nat) (UL UW : Nat → Nat) (a x : Nat) : Nat :=
  gword G (UL a) (UW a) x

@[expose] noncomputable def fFixK (G : Nat → Nat → Nat) (UL UW : Nat → Nat) : Bool :=
  bAnd(Nat.beq (mapK (evalWK (uG G UL UW) (FW 0)) BK) (mapK (fG G 0) BK),
    Nat.beq (mapK (evalWK (uG G UL UW) (FW 1)) BK) (mapK (fG G 1) BK))

@[expose] noncomputable def CX (l : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) [1, 1, 1] [1] (Nat.beq l (nat_lit 0))

@[expose] noncomputable def CY (l : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) [0, 0, 1, 1, 0, 0, 1, 0, 0] [1, 1, 0, 0, 1, 0, 0]
    (Nat.beq l (nat_lit 0))

@[expose] noncomputable def evalFK (G : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.foldr (fun a q => fG G a q) x w

@[expose] noncomputable def fCommK (G : Nat → Nat → Nat) : Bool :=
  allN (nat_lit 2) fun l =>
    Nat.beq (mapK (fun p => evalFK G (CX l) (evalFK G (CY l) p)) BK)
      (mapK (fun p => fG G l (evalFK G (CY l) (evalFK G (CX l) p))) BK)

end CFSG.KC.ONK3

end
