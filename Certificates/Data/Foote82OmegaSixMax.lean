module

public import Certificates.Data.Foote82OmegaSixCent

public section

namespace CFSG.CGT.Foote82.OmegaSix

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def cr1Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 0; 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def cr2Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def dc1Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 1]

@[expose] def dc2Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0]

@[expose] def genA6Inv (_ : Unit := ()) : Array (Array ℕ) :=
  #[marr aMat, marr (bMat * (bMat * (bMat * bMat)))]

@[expose] def reflEnum (_ : Unit := ()) : Enum := conjEnum (genA6 ()) (genA6Inv ()) (marr rMat) 40

@[expose] def genCr (_ : Unit := ()) : Array (Array ℕ) := #[marr cr1Mat, marr cr2Mat]

@[expose] def crEnum (_ : Unit := ()) : Enum := bfsEnum (genCr ()) 720

@[expose] def genCr1 (_ : Unit := ()) : Array (Array ℕ) := #[marr cr1Mat, marr cr2Mat, marr dc1Mat]

@[expose] def genCr2 (_ : Unit := ()) : Array (Array ℕ) := #[marr cr1Mat, marr cr2Mat, marr dc2Mat]

@[expose] def cr1Enum (_ : Unit := ()) : Enum := bfsEnum (genCr1 ()) 25920

@[expose] def cr2Enum (_ : Unit := ()) : Enum := bfsEnum (genCr2 ()) 25920

@[expose] def maxMatCheck (_ : Unit := ()) : Bool :=
  decide (cr1Mat * rMat = rMat * cr1Mat) && decide (cr2Mat * rMat = rMat * cr2Mat) &&
    decide (dc1Mat * dc1Mat = 1) && decide (dc2Mat * dc2Mat = 1) &&
    !decide (dc1Mat * rMat = rMat * dc1Mat)

@[expose] def maxMemCheck (_ : Unit := ()) : Bool :=
  let E := omegaEnum ()
  (E.lookup (marr cr1Mat)).isSome && (E.lookup (marr cr2Mat)).isSome &&
    (E.lookup (marr dc1Mat)).isSome && (E.lookup (marr dc2Mat)).isSome

@[expose] def crEnumCheck (_ : Unit := ()) : Bool :=
  treeOK (crEnum ()) (genCr ())

@[expose] def maxGen1Check (_ : Unit := ()) : Bool :=
  let gs := genCr1 ()
  let E := cr1Enum ()
  enumOK E gs && E.elems.size == 25920

@[expose] def maxGen2Check (_ : Unit := ()) : Bool :=
  let gs := genCr2 ()
  let E := cr2Enum ()
  enumOK E gs && E.elems.size == 25920

@[expose] def maxCosetCheck (_ : Unit := ()) : Bool :=
  let R := marr rMat
  let S1 := marr (dc1Mat * rMat * dc1Mat)
  let S2 := marr (dc2Mat * rMat * dc2Mat)
  let EC := crEnum ()
  (omegaEnum ()).elems.all fun y => compA y R == compA R y ||
    EC.elems.any fun c =>
      let cy := compA c y
      compA cy R == compA S1 cy || compA cy R == compA S2 cy

@[expose] def maxReflCheck (_ : Unit := ()) : Bool :=
  let RE := reflEnum ()
  conjTreeOK RE (genA6 ()) (genA6Inv ()) (marr rMat) &&
    (oEnum ()).elems.all fun t => !(rank1 t) || (RE.lookup t).isSome

end CFSG.CGT.Foote82.OmegaSix
