module

public import Certificates.Data.Kernel.GammaUCensusK

public section

namespace CFSG.KC.GUC

open CFSG.KC.IF4C CFSG.KC.IF4R

@[expose] noncomputable def tbOK (CG TB : Nat) : Bool :=
  allBelow 32 fun c => allBelow 32 fun m =>
    Nat.beq (look TB (Nat.add (Nat.mul 32 c) m)) (subP (five CG c) m)

@[expose] noncomputable def cellX (IX n j c : Nat) : Nat :=
  fld IX (Nat.add (Nat.mul 32 (Nat.add (Nat.mul 108 n) j)) c)

@[expose] noncomputable def cellOK (TB FT FC N IX n j T u c : Nat) : Bool :=
  allBelow 32 (fun m => !Nat.beq (look TB (Nat.add (Nat.mul 32 c) m)) u) ||
    (Nat.blt (cellX IX n j c) N && Nat.beq (look FT (cellX IX n j c)) T &&
      Nat.beq (fld FC (cellX IX n j c)) c)

@[expose] noncomputable def cellsOK (TB FT FC N IX n j T u : Nat) : Bool :=
  allBelow 32 fun c => cellOK TB FT FC N IX n j T u c

@[expose] noncomputable def pairAt (SPL : List Nat) (S0 TB FT FC N IX n j T Ti : Nat) : Bool :=
  !memN (ap12 Ti 3072) SPL || cellsOK TB FT FC N IX n j T (mulP Ti (mulP S0 T))

@[expose] noncomputable def pairOK (SPL : List Nat) (S0 TE TEi DT DTi TB FT FC N IX n j : Nat) :
    Bool :=
  pairAt SPL S0 TB FT FC N IX n j (mulP (look TE n) (look DT j)) (mulP (look DTi j) (look TEi n))

end CFSG.KC.GUC

end
