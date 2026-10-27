module

public import Certificates.Data.Kernel.SporSch.Closure

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def rowGet (T : Nat → Nat) (rw i : Nat) : Nat :=
  fld(T (Nat.shiftRight i (nat_lit 6)), Nat.mul rw (Nat.land i (nat_lit 63)), mask rw)

@[expose] noncomputable def saltOf (x : Nat) : Nat := Nat.land x (nat_lit 18446744073709551615)

@[expose] noncomputable def keyK (w s P : Nat) : Nat :=
  strictN P (fun p => strictN (mask w) (fun m =>
  strictN (saltOf (foldN s (fun q acc => Nat.add acc (Nat.mul (Nat.succ (pg w m p q))
      (nat_lit 11400714819323198485))) (nat_lit 0))) (fun salt =>
    foldN s (fun q acc => Nat.lor acc
      (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) (pg w m p q)))) salt)))

@[expose] noncomputable def imgK (w s G P : Nat) : Nat :=
  strictN G (fun g => strictN P (fun p => strictN (mask w) (fun m =>
  strictN (saltOf (foldN s (fun q acc => Nat.add acc (Nat.mul (Nat.succ (pg w m g (pg w m p q)))
      (nat_lit 11400714819323198485))) (nat_lit 0))) (fun salt =>
    foldN s (fun q acc => Nat.lor acc
      (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) (pg w m g (pg w m p q))))) salt))))

@[expose] noncomputable def parX (w s x : Nat) : Nat := fld(x, Nat.mul s w, nat_lit 1048575)

@[expose] noncomputable def labX (w s x : Nat) : Nat :=
  fld(x, Nat.add (Nat.mul s w) (nat_lit 20), nat_lit 255)

@[expose] noncomputable def eltK (n w s x : Nat) : Bool :=
  allN s (fun q => bAnd(Nat.blt (pg w (mask w) x q) n,
    bIf(Nat.beq q (nat_lit 0), true,
      Nat.blt (pg w (mask w) x (Nat.sub q (nat_lit 1))) (pg w (mask w) x q))))

@[expose] noncomputable def ptsFrom (w x : Nat) (start : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih q => bAnd(Nat.beq (pg w (mask w) x q) p, ih (Nat.succ q))) start

@[expose] noncomputable def startK (w s x : Nat) (start : List Nat) : Bool :=
  bAnd(Nat.beq (CFSG.KS.Mathieu.lenN start) s, bAnd(ptsFrom w x start (nat_lit 0),
    bAnd(Nat.beq (parX w s x) (nat_lit 0), Nat.beq (labX w s x) (nat_lit 0))))

@[expose] noncomputable def sortK (w s : Nat) (X SO SOI : Nat → Nat) (c i : Nat) : Bool :=
  strictB (SO i) (fun j => bAnd(Nat.blt j c, bAnd(Nat.beq (SOI j) i,
    bIf(Nat.blt (Nat.succ i) c, Nat.blt (keyK w s (X j)) (keyK w s (X (SO (Nat.succ i)))), true))))

@[expose] noncomputable def eltAt (n w s : Nat) (X : Nat → Nat) (c i : Nat) : Bool :=
  bIf(Nat.blt i c, strictB (X i) (fun x => eltK n w s x), true)

@[expose] noncomputable def sortAt (w s : Nat) (X SO SOI : Nat → Nat) (c i : Nat) : Bool :=
  bIf(Nat.blt i c, sortK w s X SO SOI c i, true)

@[expose] noncomputable def stepR (w s : Nat) (G X W : Nat → Nat) (c bound h k cur : Nat) : Nat :=
  nIf(Nat.beq cur bound, cur,
  nIf(Nat.blt h cur,
    strictN (imgK w s (G k) (X h)) (fun t =>
    strictN fld(W h, Nat.mul (nat_lit 20) k, nat_lit 1048575) (fun j =>
    strictN (X j) (fun xj =>
      nIf(bAnd(Nat.blt j cur, Nat.beq (keyK w s xj) t), cur,
      nIf(bAnd(Nat.beq j cur, bAnd(Nat.beq (keyK w s xj) t,
          bAnd(Nat.beq (parX w s xj) h, Nat.beq (labX w s xj) k))),
        Nat.succ cur, failC))))),
    nIf(Nat.beq cur c, cur, failC)))

@[expose] noncomputable def headR (w s : Nat) (G X W : Nat → Nat) (kg c bound h cur : Nat) : Nat :=
  foldUp kg (fun k cur => stepR w s G X W c bound h k cur) cur

@[expose] noncomputable def runFrom (w s : Nat) (G X W : Nat → Nat) (kg c bound : Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ cur => cur)
    (fun _ ih h cur => strictN (headR w s G X W kg c bound h cur) (fun c' =>
      strictN (Nat.succ h) (fun h' => ih h' c')))

end CFSG.KS.SporSch

end
