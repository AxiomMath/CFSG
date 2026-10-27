module

public import Certificates.Data.Kernel.E6Salt
public import Certificates.Data.Kernel.F4Planes

public section

namespace CFSG.KC.F4PlanesE6

open CFSG.KC.E6Salt CFSG.KC.Loop
open CFSG.KC.F4Planes (aR bR)

abbrev G4 : Type := Nat × Nat × Nat × Nat

@[expose] noncomputable def iotaB (LP IP IPi : Nat) (iw il : List Nat) : Bool :=
  allN 8 fun c => strictB (letT IP c) fun I =>
    eqS I (wordS LP 4 (iw.getD c 0) (il.getD c 0)) && eqS (mulS I (letT IPi c)) oneS

@[expose] noncomputable def pathE (Gs : List Nat) (p : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) oneS (fun k _ ih => mulS (Gs.getD k 0) ih) p

@[expose] noncomputable def pinE (IP : Nat) (gw gl : List Nat) (paths : List (List Nat))
    (pS : List Nat) : Bool :=
  strictB (wordS IP 3 (gw.getD 0 0) (gl.getD 0 0)) fun G0 =>
    strictB (wordS IP 3 (gw.getD 1 0) (gl.getD 1 0)) fun G1 =>
      strictB (wordS IP 3 (gw.getD 2 0) (gl.getD 2 0)) fun G2 =>
        strictB (wordS IP 3 (gw.getD 3 0) (gl.getD 3 0)) fun G3 =>
          strictB (wordS IP 3 (gw.getD 4 0) (gl.getD 4 0)) fun G4 =>
            allN 6 fun i => allL (paths.getD i []) (fun k => Nat.blt k 5) &&
              eqS (pathE [G0, G1, G2, G3, G4] (paths.getD i [])) (pS.getD i 0)

@[expose] noncomputable def fSE (S0 S1 S2 S3 a : Nat) : Nat :=
  mulS (mulS (mulS (powS S0 (Nat.mod a 3)) (powS S1 (Nat.mod (Nat.div a 3) 3)))
    (powS S2 (Nat.mod (Nat.div a 9) 3))) (powS S3 (Nat.mod (Nat.div a 27) 3))

@[expose] noncomputable def phiE (S0 S1 S2 S3 G4 G5 m : Nat) : Nat :=
  mulS (fSE S0 S1 S2 S3 (Nat.mod m 81))
    (mulS (powS G4 (Nat.mod (Nat.div m 81) 3)) (powS G5 (Nat.mod (Nat.div m 243) 3)))

@[expose] noncomputable def lenL {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def tokE (IP IPi : Nat) (gs : List G4) (n k : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (gs.getD (Nat.sub k (Nat.add 16 n)) (0, 0, 0, 0)).2.2.2
        (letT IPi (Nat.sub k (Nat.add 8 n))) (Nat.blt k (Nat.add 16 n)))
      (gs.getD (Nat.sub k 8) (0, 0, 0, 0)).2.2.1 (Nat.blt k (Nat.add 8 n)))
    (letT IP k) (Nat.blt k 8)

@[expose] noncomputable def prodE (IP IPi : Nat) (gs : List G4) (n : Nat) (idx : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) oneS (fun k _ ih => mulS (tokE IP IPi gs n k) ih) idx

@[expose] noncomputable def tgW (t : Nat) : Nat :=
  Bool.rec (Bool.rec 642 96 (Nat.blt t 3)) (Nat.mul 2 t) (Nat.blt t 2)

@[expose] noncomputable def tgL (t : Nat) : Nat :=
  Bool.rec 3 1 (Nat.blt t 2)

@[expose] noncomputable def genE (LP E : Nat) (g : G4) : Bool :=
  strictB g.2.2.1 fun T =>
    eqS (wordS LP 4 g.1 g.2.1) T && eqS (mulS T g.2.2.2) oneS && eqS (mulS T E) (mulS E T)

@[expose] noncomputable def tgtE (LP IP IPi : Nat) (gs : List G4) (n : Nat) (idx : List Nat)
    (t : Nat) : Bool :=
  allL idx (fun k => Nat.blt k (Nat.add 16 (Nat.add n n))) &&
    eqS (prodE IP IPi gs n idx) (wordS LP 4 (tgW t) (tgL t))

@[expose] noncomputable def rowE (LP IP IPi : Nat) (pS : List Nat) (ab ij : Nat × Nat)
    (gs : List G4) (tg : List (List Nat)) : Bool :=
  strictB (pS.getD 0 0) fun S0 => strictB (pS.getD 1 0) fun S1 =>
    strictB (pS.getD 2 0) fun S2 => strictB (pS.getD 3 0) fun S3 =>
      strictB (pS.getD 4 0) fun G4 => strictB (pS.getD 5 0) fun G5 =>
        strictB (phiE S0 S1 S2 S3 G4 G5 ab.1) fun A =>
          strictB (phiE S0 S1 S2 S3 G4 G5 ab.2) fun B =>
            strictB (mulS (powS A ij.1) (powS B ij.2)) fun E =>
              !eqS E oneS && allL gs (genE LP E) &&
                strictB (lenL gs) fun n => allN 4 fun t => tgtE LP IP IPi gs n (tg.getD t []) t

@[expose] noncomputable def rowAt (LP IP IPi : Nat) (pS : List Nat) (PR : Nat)
    (ij : List (Nat × Nat)) (gens : List (List G4)) (tgs : List (List (List Nat))) (r : Nat) :
    Bool :=
  rowE LP IP IPi pS (aR PR r, bR PR r) (ij.getD r (0, 0)) (gens.getD r []) (tgs.getD r [])

end CFSG.KC.F4PlanesE6

end
