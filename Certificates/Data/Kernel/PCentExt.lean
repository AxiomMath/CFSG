module

public import Certificates.Data.Kernel.PCent

public section

namespace CFSG.KC.PCent

open CFSG.KC.Enum (pg pcomp pidn allN)
open CFSG.KS (mask pinvS)

@[expose] noncomputable def conjP (n w x y : Nat) : Nat :=
  pcomp n w (mask w) x (pcomp n w (mask w) y (pinvS n w (mask w) x))

@[expose] noncomputable def commP (n w x y : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) x y)
    (pcomp n w (mask w) (pinvS n w (mask w) x) (pinvS n w (mask w) y))

@[expose] noncomputable def wordEqK (n w : Nat) (D : Nat → Nat) (nd x : Nat) (ws : List Nat) :
    Bool :=
  allL (fun c => Nat.blt c nd) ws && Nat.beq x (wordK n w D ws)

@[expose] noncomputable def normK (n w : Nat) (M : Nat → Nat) (nm : Nat) (D : Nat → Nat) (nd : Nat)
    (W : List (List Nat)) : Bool :=
  allN nm (fun a => allN nd (fun b =>
    wordEqK n w D nd (conjP n w (M a) (D b)) (W.getD (Nat.add (Nat.mul a nd) b) []) &&
      wordEqK n w D nd (conjP n w (pinvS n w (mask w) (M a)) (D b))
        (W.getD (Nat.add (Nat.mul nm nd) (Nat.add (Nat.mul a nd) b)) []))) &&
    allN nm (fun a => allN nm (fun c =>
      wordEqK n w D nd (commP n w (M a) (M c))
        (W.getD (Nat.add (Nat.mul (nat_lit 2) (Nat.mul nm nd)) (Nat.add (Nat.mul a nm) c)) [])))

@[expose] noncomputable def baseInK (L : List (Nat × List Nat × List (List Nat) × List Rec))
    (OM : Nat) : Bool :=
  allL (fun x => Nat.testBit OM x) (L.map Prod.fst)

end CFSG.KC.PCent

end
