module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.PermAdj

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.LQT.P (anyN)

@[expose] noncomputable def invoK (n w p : Nat) : Bool :=
  !(Nat.beq p (pidn n w)) && Nat.beq (pcomp n w (mask w) p p) (pidn n w)

@[expose] noncomputable def adjK (n w p q : Nat) : Bool := invoK n w (pcomp n w (mask w) p q)

@[expose] noncomputable def fixedK (n w p : Nat) : Bool := anyN n fun i => Nat.beq (pg w (mask w) p i) i

@[expose] noncomputable def nbrPt (n w M X : Nat) (T NB INV : Nat → Nat) (i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (!(adjK n w X (T i))) (adjK n w X (T i))
    (Nat.blt (INV i) M && Nat.beq (NB (INV i)) i)

@[expose] noncomputable def nbPt (n w N X : Nat) (T NB : Nat → Nat) (j : Nat) : Bool :=
  Nat.blt (NB j) N && adjK n w X (T (NB j))

@[expose] noncomputable def cliquePt (n w M X : Nat) (T NB : Nat → Nat) (j : Nat) : Bool :=
  strictB (T (NB j)) fun b => fixedK n w (pcomp n w (mask w) X b) ||
    allN M fun j1 => !(adjK n w b (T (NB j1))) ||
      allN M fun j2 => !(adjK n w b (T (NB j2))) || !(adjK n w (T (NB j1)) (T (NB j2)))

end CFSG.KC.PermAdj

end
