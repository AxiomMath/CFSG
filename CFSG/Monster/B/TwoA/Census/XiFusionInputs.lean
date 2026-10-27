module

public import CFSG.Monster.B.TwoA.Census.MonoXi
public import CFSG.Monster.B.TwoA.Census.MonoClasses
public import CFSG.Monster.Visible.XiPair
public import CFSG.Monster.VisQuot.Image
public import CFSG.Monster.B.TwoA.Census.DenseMat
public meta import CFSG.Monster.B.TwoA.Census.DenseMat
public meta import CFSG.Monster.B.TwoA.Census.MonoXi
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public meta import CFSG.Monster.Xi.Defs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.Xi Matrix

@[expose] def dsgn (d : ℕ) : Matrix (Fin 24) (Fin 24) ℚ :=
  diagonal fun k => if d.testBit k then -1 else 1

@[expose] def pmatA (a : Array ℕ) : Matrix (Fin 24) (Fin 24) ℚ :=
  Matrix.of fun i j => if a[(i : ℕ)]! = (j : ℕ) then 1 else 0

@[expose] def letterArr (l : ℕ) : Array ℕ := (centGenArrs 0).getD (if l = 0 then 0 else 1) #[]

@[expose] def wordArr : List ℕ → Array ℕ
  | [] => idArr
  | a :: w => amul (wordArr w) (letterArr a)

@[expose] def xiArrA (e : XiEdge) : Array (Array ℚ) :=
  mulArr (ofMat (dsgn (monoSign.getD e.source 0)))
    (ofMat (pmatA (seedA (monoSeed.getD e.source 0))))

@[expose] def xiArrM (e : XiEdge) : Array (Array ℚ) :=
  mulArr (mulArr (ofMat (dsgn e.conjSign)) (ofMat (pmatA (wordArr e.word)))) (ofMat gXi)

@[expose] def xiArrR (e : XiEdge) : Array (Array ℚ) :=
  mulArr (ofMat (dsgn e.afterSign)) (ofMat (pmatA e.afterPerm))

end CFSG.Monster.B.TwoA.Census
