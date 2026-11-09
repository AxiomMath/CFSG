module

public import Certificates.Data.Kernel.Spor.Fi24Sev

public section

namespace CFSG.KC.Fi24SevB

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev

@[expose] noncomputable def pw (w : List Nat) (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil (fun _ ih => w ++ ih) n

@[expose] noncomputable def agB (NW : Nat → Nat → Nat) (NT : Nat → Nat) (u v : List Nat) : Bool :=
  allL (fun b => Nat.beq (ptC NW NT u b) (ptC NW NT v b)) cb

@[expose] noncomputable def eqOK (NW : Nat → Nat → Nat) (NT : Nat → Nat)
    (ps : List (List Nat × List Nat)) : Bool :=
  allL (fun p => agB NW NT p.1 p.2) ps

@[expose] noncomputable def neOK (NW : Nat → Nat → Nat) (NT : Nat → Nat)
    (ps : List (List Nat × List Nat)) : Bool :=
  allL (fun p => notB (agB NW NT p.1 p.2)) ps

@[expose] noncomputable def slIn (NW : Nat → Nat → Nat) (NT : Nat → Nat)
    (sl part : List (Nat × List Nat × List Nat)) : Bool :=
  allL (fun e => andB
      (allL (fun z => andB (Nat.ble (nat_lit 2) z) (orB (Nat.ble z (nat_lit 5))
        (andB (Nat.blt (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)) e.1)
          (hasU sl (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)))))) e.2.1)
      (agB NW NT (expU sl e.2.1) e.2.2)) part

@[expose] noncomputable def mW (sl : List (Nat × List Nat × List Nat)) (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun l _ ih => lIf (Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 0))
      (findU sl (Nat.shiftRight l (nat_lit 1))) (invC (findU sl (Nat.shiftRight l (nat_lit 1)))) ++ ih) w

@[expose] noncomputable def cubeW (sl : List (Nat × List Nat × List Nat)) (t : Nat) : List Nat :=
  pw (findU sl (nat_lit 64)) (Nat.div t (nat_lit 49)) ++
    (pw (findU sl (nat_lit 66)) (Nat.mod (Nat.div t (nat_lit 7)) (nat_lit 7)) ++
      pw (findU sl (nat_lit 67)) (Nat.mod t (nat_lit 7)))

@[expose] noncomputable def cjOK (NW : Nat → Nat → Nat) (NT : Nat → Nat)
    (sl : List (Nat × List Nat × List Nat)) (c : Nat × Nat × List Nat × List Nat) : Bool :=
  andB (allL (fun l => hasU sl (Nat.shiftRight l (nat_lit 1))) c.2.2.1)
    (andB (agB NW NT (mW sl c.2.2.1) c.2.2.2)
      (agB NW NT (c.2.2.2 ++ cubeW sl c.1)
        (lIf (Nat.beq c.2.1 (nat_lit 0)) (findU sl (nat_lit 66)) (findU sl (nat_lit 67)) ++ c.2.2.2)))

@[expose] noncomputable def fixK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (w : List Nat) (n : Nat) :
    Bool :=
  Nat.beq (popcount (fixC NW NT w) (nat_lit 524288)) n

@[expose] noncomputable def mk12 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)) (nat_lit 1)

@[expose] noncomputable def bitK (m q : Nat) : Nat :=
  strictN (Nat.shiftRight q (nat_lit 12)) (fun a =>
    Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight m (Nat.shiftLeft a (nat_lit 12))) mk12)
      (Nat.land q (nat_lit 4095))) (nat_lit 1))

@[expose] noncomputable def swpB (d m q : Nat) : Nat :=
  nIf(Nat.beq (bitK m q) (nat_lit 1), Nat.add q d,
    nIf(Nat.ble d q,
      nIf(Nat.beq (bitK m (Nat.sub q d)) (nat_lit 1), Nat.sub q d, q),
      q))

@[expose] noncomputable def ptFB (M : Nat → Nat) (q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) q
    (fun j ih => strictN ih (fun y => swpB (ldist (Nat.sub (nat_lit 36) j))
      (M (Nat.sub (nat_lit 36) j)) y)) (nat_lit 37)

@[expose] noncomputable def ptRB (M : Nat → Nat) (q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) q
    (fun j ih => strictN ih (fun y => swpB (ldist j) (M j) y)) (nat_lit 37)

@[expose] noncomputable def letNB (NW : Nat → Nat → Nat) (l x : Nat) : Nat :=
  nIf(Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 0), ptFB (NW (Nat.shiftRight l (nat_lit 1))) x,
    ptRB (NW (Nat.shiftRight l (nat_lit 1))) x)

@[expose] noncomputable def apCB (NW : Nat → Nat → Nat) (NT : Nat → Nat) (c x : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 26), ptFB NT x, letNB NW c x)

@[expose] noncomputable def ptCB (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) (x : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat) x (fun c _ ih => strictN ih (apCB NW NT c)) cs

@[expose] noncomputable def agBB (NW : Nat → Nat → Nat) (NT : Nat → Nat) (u v : List Nat) : Bool :=
  allL (fun b => Nat.beq (ptCB NW NT u b) (ptCB NW NT v b)) cb

@[expose] noncomputable def slInB (NW : Nat → Nat → Nat) (NT : Nat → Nat)
    (sl part : List (Nat × List Nat × List Nat)) : Bool :=
  allL (fun e => andB
      (allL (fun z => andB (Nat.ble (nat_lit 2) z) (orB (Nat.ble z (nat_lit 5))
        (andB (Nat.blt (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)) e.1)
          (hasU sl (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)))))) e.2.1)
      (agBB NW NT (expU sl e.2.1) e.2.2)) part

end CFSG.KC.Fi24SevB

end
