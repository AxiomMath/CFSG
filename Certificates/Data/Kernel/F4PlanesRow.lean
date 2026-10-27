module

public import Certificates.Data.Kernel.F4Planes
public import Certificates.Data.Kernel.F4Syl3Cls

public section

namespace CFSG.KC.F4Planes

open CFSG.KC.F4Salt CFSG.KC.Loop CFSG.KC.F4Syl3

abbrev G6 : Type := Nat × Nat × Nat × Nat × Nat × Nat

@[expose] noncomputable def pathS (Gs : List Nat) (p : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) oneS (fun k _ ih => mulS (Gs.getD k 0) ih) p

@[expose] noncomputable def pinP (gw gl : List Nat) (paths : List (List Nat)) (pS : List Nat) :
    Bool :=
  strictB (wordS (gw.getD 0 0) (gl.getD 0 0)) fun G0 =>
    strictB (wordS (gw.getD 1 0) (gl.getD 1 0)) fun G1 =>
      strictB (wordS (gw.getD 2 0) (gl.getD 2 0)) fun G2 =>
        strictB (wordS (gw.getD 3 0) (gl.getD 3 0)) fun G3 =>
          strictB (wordS (gw.getD 4 0) (gl.getD 4 0)) fun G4 =>
            allN 6 fun i => allL (paths.getD i []) (fun k => Nat.blt k 5) &&
              eqS (pathS [G0, G1, G2, G3, G4] (paths.getD i [])) (pS.getD i 0)

@[expose] noncomputable def relP (pS : List Nat) : Bool :=
  strictB (pS.getD 0 0) fun S0 => strictB (pS.getD 1 0) fun S1 =>
    strictB (pS.getD 2 0) fun S2 => strictB (pS.getD 3 0) fun S3 =>
      strictB (pS.getD 4 0) fun G4 => strictB (pS.getD 5 0) fun G5 =>
        relB [S0, S1, S2, S3] G4 G5

@[expose] noncomputable def lenL {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def tokAt (gs : List G6) (n k : Nat) : Nat :=
  Bool.rec (gs.getD (Nat.sub k n) (0, 0, 0, 0, 0, 0)).2.2.2.2.2
    (gs.getD k (0, 0, 0, 0, 0, 0)).2.2.2.2.1 (Nat.blt k n)

@[expose] noncomputable def prodTok (gs : List G6) (n : Nat) (idx : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) oneS (fun k _ ih => mulS (tokAt gs n k) ih) idx

@[expose] noncomputable def genB (A B : Nat) (g : G6) : Bool :=
  strictB (mulS (powS A g.2.2.1) (powS B g.2.2.2.1)) fun E =>
    strictB g.2.2.2.2.1 fun T =>
      eqS (wordS g.1 g.2.1) T && eqS (mulS T g.2.2.2.2.2) oneS && !eqS E oneS &&
        eqS (mulS T E) (mulS E T)

@[expose] noncomputable def twW (t : Nat) : Nat :=
  Bool.rec (Nat.add (Nat.add (Nat.sub t 4) (Nat.mul 8 t)) (Nat.mul 64 (Nat.sub t 4))) t
    (Nat.blt t 4)

@[expose] noncomputable def twL (t : Nat) : Nat :=
  Bool.rec 3 1 (Nat.blt t 4)

@[expose] noncomputable def tgtB (gs : List G6) (n : Nat) (idx : List Nat) (t : Nat) : Bool :=
  allL idx (fun k => Nat.blt k (Nat.add n n)) && eqS (prodTok gs n idx) (wordS (twW t) (twL t))

@[expose] noncomputable def rowG (S : List Nat) (G4 G5 PR : Nat) (gs : List G6)
    (tg : List (List Nat)) (r : Nat) : Bool :=
  strictB (phiS S G4 G5 (aR PR r)) fun A => strictB (phiS S G4 G5 (bR PR r)) fun B =>
    allL gs (genB A B) && strictB (lenL gs) fun n => allN 8 fun t => tgtB gs n (tg.getD t []) t

@[expose] noncomputable def rowP (pS : List Nat) (PR : Nat) (gens : List (List G6))
    (tgs : List (List (List Nat))) (r : Nat) : Bool :=
  strictB (pS.getD 0 0) fun S0 => strictB (pS.getD 1 0) fun S1 =>
    strictB (pS.getD 2 0) fun S2 => strictB (pS.getD 3 0) fun S3 =>
      strictB (pS.getD 4 0) fun G4 => strictB (pS.getD 5 0) fun G5 =>
        rowG [S0, S1, S2, S3] G4 G5 PR (gens.getD r []) (tgs.getD r []) r

end CFSG.KC.F4Planes

end
