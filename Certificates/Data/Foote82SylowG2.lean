module

public import Certificates.Data.Foote82OmegaSix
public import Mathlib.Algebra.Group.End
public import Mathlib.Logic.Equiv.Basic

public section

namespace CFSG.CGT.Foote82.CaseIIG2Aux

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.CGT.Foote82.OmegaSix Equiv

@[expose] def permArr {n : ℕ} (σ : Perm (Fin n)) : Array ℕ :=
  Array.ofFn (n := 64) fun i => if h : i.val < n then (σ ⟨i.val, h⟩).val else i.val

@[expose] def pMat1 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 1, 0, 1, 0; 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 1;
    0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0]

@[expose] def pMat2 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 1, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0;
    1, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def pMat3 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 1, 0, 1, 1, 0; 1, 1, 1, 1, 0, 0; 1, 0, 0, 1, 0, 0;
    0, 1, 1, 1, 1, 0; 0, 0, 0, 0, 1, 0; 0, 1, 1, 0, 1, 1]

@[expose] def tPerm1 : Perm (Fin 10) := swap 0 1 * swap 8 9

@[expose] def tPerm2 : Perm (Fin 10) := swap 0 2 * swap 1 3

@[expose] def tPerm3 : Perm (Fin 10) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

@[expose] def genP (_ : Unit := ()) : Array (Array ℕ) := #[marr pMat1, marr pMat2, marr pMat3]

@[expose] def genT (_ : Unit := ()) : Array (Array ℕ) :=
  #[permArr tPerm1, permArr tPerm2, permArr tPerm3]

@[expose] def enumP (_ : Unit := ()) : Enum := bfsEnum (genP ()) 128

@[expose] def pEnumCheck (_ : Unit := ()) : Bool :=
  let gs := genP ()
  let E := enumP ()
  enumOK E gs && E.elems.size == 128

@[expose] def pAutCheck (_ : Unit := ()) : Bool :=
  let gs := genP ()
  let hs := genT ()
  let E := enumP ()
  autOK E gs hs (buildF E hs)

@[expose] def cMat1 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 0, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 1, 0;
    1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 1, 0, 0, 1, 0, 1]

@[expose] def dMat1 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 1, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0;
    1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1]

@[expose] def dInvMat1 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 0, 1, 1, 0, 0; 1, 1, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 1, 1]

@[expose] def cMat2 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def dMat2 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 0, 1, 1, 0, 0; 1, 1, 1, 1, 0, 0; 1, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1]

@[expose] def dInvMat2 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 0, 1, 1, 0, 0; 1, 1, 1, 1, 0, 0; 1, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0]

@[expose] def cMat3 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 0, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 1, 0;
    1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 1, 0, 0, 1, 0, 1]

@[expose] def dMat3 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def dInvMat3 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def uPerm1 : Perm (Fin 8) := swap 0 1 * swap 4 5

@[expose] def uPerm2 : Perm (Fin 8) := swap 0 2 * swap 1 3

@[expose] def uPerm3 : Perm (Fin 8) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

@[expose] def genQ (_ : Unit := ()) : Array (Array ℕ) :=
  #[marr (cMat1 * dMat1 * cMat1 * dInvMat1), marr (cMat2 * dMat2 * cMat2 * dInvMat2),
    marr (cMat3 * dMat3 * cMat3 * dInvMat3)]

@[expose] def genU (_ : Unit := ()) : Array (Array ℕ) :=
  #[permArr uPerm1, permArr uPerm2, permArr uPerm3]

@[expose] def enumQ (_ : Unit := ()) : Enum := bfsEnum (genQ ()) 64

@[expose] def qEnumCheck (_ : Unit := ()) : Bool :=
  let gs := genQ ()
  let E := enumQ ()
  enumOK E gs && E.elems.size == 64

@[expose] def qAutCheck (_ : Unit := ()) : Bool :=
  let gs := genQ ()
  let hs := genU ()
  let E := enumQ ()
  autOK E gs hs (buildF E hs)

end CFSG.CGT.Foote82.CaseIIG2Aux
