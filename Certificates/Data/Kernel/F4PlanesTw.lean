module

public import Certificates.Data.Kernel.F4PlanesE6

public section

namespace CFSG.KC.F4PlanesTw

open CFSG.KC.E6Salt CFSG.KC.Loop
open CFSG.KC.F4PlanesE6 (phiE lenL)
open CFSG.KC.F4Planes (aR bR)

abbrev G3 : Type := Nat × Nat × Nat

@[expose] noncomputable def pr (A B : Nat) : Nat :=
  Nat.add (Nat.mod A (Nat.pow 2 6400)) (Nat.shiftLeft B 6400)

@[expose] noncomputable def fa (P : Nat) : Nat :=
  Nat.mod P (Nat.pow 2 6400)

@[expose] noncomputable def fb (P : Nat) : Nat :=
  Nat.shiftRight P 6400

@[expose] noncomputable def mul2 (P Q : Nat) : Nat :=
  strictN (fa P) fun A => strictN (fb P) fun B => strictN (fa Q) fun C => strictN (fb Q) fun D =>
    strictN (mulS A C) fun AC =>
      pr (Nat.xor AC (mulS B D)) (Nat.xor (mulS (Nat.xor A B) (Nat.xor C D)) AC)

@[expose] noncomputable def eq2 (P Q : Nat) : Bool :=
  eqS (fa P) (fa Q) && eqS (fb P) (fb Q)

@[expose] noncomputable def one2 : Nat :=
  pr oneS 0

@[expose] noncomputable def letP (IP X8 X9 c : Nat) : Nat :=
  Bool.rec (Bool.rec X9 X8 (Nat.beq c 8)) (pr (letT IP c) 0) (Nat.blt c 8)

@[expose] noncomputable def wordPAux (IP X8 X9 W : Nat) (m : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun m ih acc => strictN (mul2 (letP IP X8 X9 (digit 4 W m)) acc) ih) m

@[expose] noncomputable def wordP (IP X8 X9 W L : Nat) : Nat :=
  wordPAux IP X8 X9 W L one2

@[expose] noncomputable def tokP (IP : Nat) (gs : List G3) (k : Nat) : Nat :=
  Bool.rec (gs.getD (Nat.sub k 8) (0, 0, 0)).2.2 (pr (letT IP k) 0) (Nat.blt k 8)

@[expose] noncomputable def prodP (IP : Nat) (gs : List G3) (idx : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) one2 (fun k _ ih => mul2 (tokP IP gs k) ih) idx

@[expose] noncomputable def genP (IP X8 X9 E : Nat) (g : G3) : Bool :=
  strictB g.2.2 fun T => eq2 (wordP IP X8 X9 g.1 g.2.1) T && eq2 (mul2 T E) (mul2 E T)

@[expose] noncomputable def tgtP (IP : Nat) (gs : List G3) (n : Nat) (idx : List Nat) (X : Nat) :
    Bool :=
  allL idx (fun k => Nat.blt k (Nat.add 8 n)) && eq2 (prodP IP gs idx) X

@[expose] noncomputable def rowT (IP X8 X9 : Nat) (pS : List Nat) (ab ij : Nat × Nat)
    (gs : List G3) (zs : List (List Nat)) : Bool :=
  strictB (pS.getD 0 0) fun S0 => strictB (pS.getD 1 0) fun S1 =>
    strictB (pS.getD 2 0) fun S2 => strictB (pS.getD 3 0) fun S3 =>
      strictB (pS.getD 4 0) fun G4 => strictB (pS.getD 5 0) fun G5 =>
        strictB (phiE S0 S1 S2 S3 G4 G5 ab.1) fun A =>
          strictB (phiE S0 S1 S2 S3 G4 G5 ab.2) fun B =>
            strictB (mulS (powS A ij.1) (powS B ij.2)) fun E =>
              !eqS E oneS && strictB (pr E 0) fun E2 => allL gs (genP IP X8 X9 E2) &&
                strictB (lenL gs) fun n =>
                  tgtP IP gs n (zs.getD 0 []) X8 && tgtP IP gs n (zs.getD 1 []) X9

@[expose] noncomputable def rowAtT (IP X8 X9 : Nat) (pS : List Nat) (PR : Nat)
    (ij : List (Nat × Nat)) (gens : List (List G3)) (zs : List (List (List Nat))) (r : Nat) :
    Bool :=
  rowT IP X8 X9 pS (aR PR r, bR PR r) (ij.getD r (0, 0)) (gens.getD r []) (zs.getD r [])

end CFSG.KC.F4PlanesTw

end
