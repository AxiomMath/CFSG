module

public import Certificates.Data.Kernel.Spor.Fi24ThreeO

public section

namespace CFSG.KC.Fi24Sev

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO

@[expose] noncomputable def getP (Z i : Nat) : Nat :=
  Nat.land (Nat.shiftRight Z (Nat.mul i (nat_lit 20))) (nat_lit 1048575)

@[expose] noncomputable def putP (Z i x : Nat) : Nat :=
  Nat.lor Z (Nat.shiftLeft x (Nat.mul i (nat_lit 20)))

@[expose] noncomputable def tupA (f : Nat → Nat) (n : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ Z => Z)
    (fun _ ih i x Z => strictN (putP Z i x) (fun Z' => strictN (f x) (fun y => ih (Nat.succ i) y Z'))) n

@[expose] noncomputable def tupP (f : Nat → Nat) (q : Nat) : Nat := tupA f (nat_lit 7) (nat_lit 0) q (nat_lit 0)

@[expose] noncomputable def cfgP (OL NT : Nat → Nat) (prog : List (Nat × Nat)) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ Z => Z)
    (fun p _ ih n Z => strictN (clsK OL NT (getP Z p.1) (getP Z p.2)) (fun x =>
      strictN (putP Z n x) (ih (Nat.succ n)))) prog

@[expose] noncomputable def nthD {α : Type} (d : α) (l : List α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih j => Nat.rec (motive := fun _ => α) a (fun k _ => ih k) j) l i

@[expose] noncomputable def cfgT (NW : Nat → Nat → Nat) (NT OL : Nat → Nat) (w : List Nat)
    (prog : List (Nat × Nat)) (q : Nat) : Nat :=
  cfgP OL NT prog (nat_lit 7) (tupP (ptC NW NT w) q)

@[expose] noncomputable def refOK (NW : Nat → Nat → Nat) (NT OL : Nat → Nat) (w : List Nat) (To q : Nat)
    (c : List (Nat × Nat) × Nat × Nat × Nat) : Bool :=
  letB (cfgP OL NT c.1 c.2.2.2
      (Nat.land To (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul c.2.2.2 (nat_lit 20))) (nat_lit 1))))
    (fun Zo => letB (cfgP OL NT c.1 c.2.2.2 (tupA (ptC NW NT w) c.2.2.2 (nat_lit 0) q (nat_lit 0)))
      (fun Zq => andB (Nat.beq (getP Zq c.2.1) (getP Zq c.2.2.1))
        (notB (Nat.beq (getP Zo c.2.1) (getP Zo c.2.2.1)))))

@[expose] noncomputable def refsOK (NW : Nat → Nat → Nat) (NT OL : Nat → Nat) (w : List Nat) (om : Nat)
    (reps : List Nat) (rf : List (List (Nat × Nat) × Nat × Nat × Nat)) : Bool :=
  letB (tupP (ptC NW NT w) om) (fun To =>
    allI (fun i c => refOK NW NT OL w To (nthD (nat_lit 0) reps i) c) rf (nat_lit 0))

@[expose] noncomputable def baseOK (NW : Nat → Nat → Nat) (NT OL : Nat → Nat) (w : List Nat) (om : Nat)
    (prog : List (Nat × Nat)) (pos hw bs : List Nat) : Bool :=
  andB (Nat.beq (lenL pos) (lenL bs))
    (letB (cfgT NW NT OL w prog om) (fun Z =>
      allI (fun i k => Nat.beq (ptC NW NT hw (nthD (nat_lit 0) bs i)) (getP Z k)) pos (nat_lit 0)))

@[expose] noncomputable def cb : List Nat :=
  [nat_lit 0, nat_lit 305530, nat_lit 5604, nat_lit 221549, nat_lit 266275, nat_lit 186844]

@[expose] noncomputable def pickP (Z : Nat) (pos : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ A => A)
    (fun k _ ih i A => strictN (putP A i (getP Z k)) (ih (Nat.succ i))) pos (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def mapP (f : Nat → Nat) (n C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i A => strictN A (fun A' => strictN (f (getP C i)) (putP A' i))) n

@[expose] noncomputable def lvW (i : Nat) (t : List Nat) : Bool :=
  allL (fun l => andB (Nat.ble (Nat.mul (nat_lit 4) i) l) (Nat.blt l (nat_lit 26))) t

@[expose] noncomputable def stripP (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ts : List (List Nat)) :
    Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ C => C)
    (fun t _ ih i C => nIf(andB (lvW i t) (Nat.beq (ptC NW NT t (nthD (nat_lit 0) cb i)) (getP C i)),
      strictN (mapP (ptC NW NT (invC t)) (nat_lit 6) C) (ih (Nat.succ i)),
      Nat.shiftLeft (nat_lit 1) (nat_lit 120))) ts

@[expose] noncomputable def twinOK (NW : Nat → Nat → Nat) (NT OL : Nat → Nat) (w : List Nat) (q : Nat)
    (prog : List (Nat × Nat)) (pos : List Nat) (ts : List (List Nat)) : Bool :=
  andB (Nat.beq (lenL ts) (nat_lit 5)) (andB (Nat.beq (lenL pos) (nat_lit 6))
    (letB (stripP NW NT ts (nat_lit 0) (pickP (cfgT NW NT OL w prog q) pos)) (fun C =>
      andB (Nat.blt C (Nat.shiftLeft (nat_lit 1) (nat_lit 120))) (letB (getP C (nat_lit 5)) (fun x =>
        andB (notB (Nat.beq x (nat_lit 186844))) (andB (notB (Nat.beq x (letN NW (nat_lit 24) (nat_lit 186844))))
          (notB (Nat.beq x (letN NW (nat_lit 24) (letN NW (nat_lit 24) (nat_lit 186844)))))))))))

@[expose] noncomputable def relOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (w : List Nat)
    (hs : List (List Nat)) : Bool :=
  andB (allL (fun b => Nat.beq (itN (ptC NW NT w) (nat_lit 7) b) b) cb)
    (allL (fun h => allL (fun b => Nat.beq (ptC NW NT (h ++ w) b) (ptC NW NT (w ++ h) b)) cb) hs)

@[expose] noncomputable def covOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat))
    (d : Nat) (reps : List Nat) (d2 om c : Nat) : Bool :=
  letB (iterW NW NT ws d2 (Nat.shiftLeft (nat_lit 1) om)) (fun F =>
    andB (covW NW NT ws d (plOf reps) F) (Nat.beq (popcount F (nat_lit 524288)) c))

@[expose] noncomputable def findU (sl : List (Nat × List Nat × List Nat)) (k : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun e _ ih => Bool.rec (motive := fun _ => List Nat) ih e.2.2 (Nat.beq e.1 k)) sl

@[expose] noncomputable def hasU (sl : List (Nat × List Nat × List Nat)) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ ih => orB (Nat.beq e.1 k) ih) sl

@[expose] noncomputable def lIf (c : Bool) (t e : List Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) e t c

@[expose] noncomputable def letU (sl : List (Nat × List Nat × List Nat)) (e : Nat) : List Nat :=
  lIf (Nat.ble e (nat_lit 5))
    (lIf (Nat.ble e (nat_lit 3)) (lIf (Nat.beq e (nat_lit 2)) [nat_lit 0] [nat_lit 1])
      (lIf (Nat.beq e (nat_lit 4)) [nat_lit 2] [nat_lit 3]))
    (lIf (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 0))
      (findU sl (Nat.sub (Nat.shiftRight e (nat_lit 1)) (nat_lit 3)))
      (invC (findU sl (Nat.sub (Nat.shiftRight e (nat_lit 1)) (nat_lit 3)))))

@[expose] noncomputable def expU (sl : List (Nat × List Nat × List Nat)) (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun e _ ih => letU sl e ++ ih) w

@[expose] noncomputable def slOK (NW : Nat → Nat → Nat) (NT : Nat → Nat)
    (sl : List (Nat × List Nat × List Nat)) : Bool :=
  allL (fun e => andB
      (allL (fun z => andB (Nat.ble (nat_lit 2) z) (orB (Nat.ble z (nat_lit 5))
        (andB (Nat.blt (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)) e.1)
          (hasU sl (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)))))) e.2.1)
      (allL (fun b => Nat.beq (ptC NW NT (expU sl e.2.1) b) (ptC NW NT e.2.2 b)) cb)) sl

end CFSG.KC.Fi24Sev

end
