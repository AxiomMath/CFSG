module

public import Certificates.Data.Kernel.IdxFourChainK

public section

namespace CFSG.KC.GUS

open CFSG.KC.IF4C

@[expose] noncomputable def cmP (a a' b b' : Nat) : Nat := mulP a (mulP b (mulP a' b'))

@[expose] noncomputable def unpack (NI n : Nat) : List Nat := (List.range n).map (look NI)

@[expose] noncomputable def pgP (NG : List Nat) (NI : Nat) (cp : List (Nat × Nat)) : List Nat :=
  cp.map fun p => cmP (nthD 0 NG p.1) (look NI p.1) (nthD 0 NG p.2) (look NI p.2)

@[expose] noncomputable def pgI (NG : List Nat) (NI : Nat) (cp : List (Nat × Nat)) : List Nat :=
  cp.map fun p => cmP (nthD 0 NG p.2) (look NI p.2) (nthD 0 NG p.1) (look NI p.1)

@[expose] noncomputable def dgP (PG PI : List Nat) (pp : List (Nat × Nat)) : List Nat :=
  pp.map fun p => cmP (nthD 0 PG p.1) (nthD 0 PI p.1) (nthD 0 PG p.2) (nthD 0 PI p.2)

@[expose] noncomputable def targets (NG : List Nat) (NI : Nat) (cp : List (Nat × Nat))
    (t c : Nat) : List Nat :=
  let n := lenN NG
  let PG := pgP NG NI cp
  PG ++ (List.range n).flatMap (fun a => (List.range n).map fun b =>
      cmP (nthD 0 NG a) (look NI a) (nthD 0 NG b) (look NI b)) ++
    (List.range n).flatMap (fun a => PG.map fun p => mulP (nthD 0 NG a) (mulP p (look NI a))) ++
    [t, c]

@[expose] noncomputable def pairsOK (cp : List (Nat × Nat)) (n : Nat) : Bool :=
  cp.all fun p => Nat.blt p.1 n && Nat.blt p.2 n

@[expose] noncomputable def rowsOK (r : List Nat) : Bool :=
  Nat.beq (lenN r) 12 && r.all fun x => Nat.blt x 4096

@[expose] noncomputable def invsOK (NG : List Nat) (NI : Nat) : Bool :=
  (List.range (lenN NG)).all fun l =>
    Nat.beq (mulP (nthD 0 NG l) (look NI l)) idP && Nat.beq (mulP (look NI l) (nthD 0 NG l)) idP

@[expose] noncomputable def wordG (gs w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idP (fun l _ ih => mulP (nthD 0 gs l) ih) w

@[expose] noncomputable def wordsG (gs : List Nat) (ws : List (List Nat)) (ts : List Nat) : Bool :=
  Nat.beq (lenN ws) (lenN ts) &&
    (List.zip ws ts).all fun p => p.1.all (fun l => Nat.blt l (lenN gs)) &&
      Nat.beq (wordG gs p.1) p.2

@[expose] noncomputable def stabOK (gs S : List Nat) : Bool :=
  S.all fun x => gs.all fun g => memN (ap12 g x) S

@[expose] noncomputable def reachRecs (gs OL : List Nat) (es : List (List Nat)) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih x =>
      Nat.blt (nthD 0 e 0) x && Nat.blt (nthD 0 e 1) (lenN gs) &&
        Nat.beq (ap12 (nthD 0 gs (nthD 0 e 1)) (nthD 0 OL (nthD 0 e 0))) (nthD 0 OL x) &&
        ih (Nat.succ x)) es x

@[expose] noncomputable def reachOK (gs : List Nat) (a : Nat) (OL : List Nat)
    (OT : List (List Nat)) (S : List Nat) : Bool :=
  Nat.beq (nthD 0 OL 0) a && Nat.beq (lenN OL) (Nat.succ (lenN OT)) && reachRecs gs OL OT 1 &&
    S.all fun s => memN s OL

@[expose] noncomputable def ncOK (c : Nat) (B : List Nat) (p : Nat) : Bool :=
  B.all (fun b => Nat.beq (ap12 c b) b) && !Nat.beq (mulP c p) (mulP p c)

end CFSG.KC.GUS

end
