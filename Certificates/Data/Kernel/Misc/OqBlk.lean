module

public import Certificates.Data.Kernel.Misc.Oq
public import Certificates.Data.Kernel.Misc.Base
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqInputs
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataKill
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.Misc.Oq

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def getLL (L : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun x _ _ => x) (dropK i L)

@[expose] noncomputable def partsL : List (List Nat) :=
  [stabPL0, stabPL1, stabPL2, stabPL3, stabPL4, stabPL5, stabPL6, stabPL7, stabPL8]

@[expose] noncomputable def partsU : List (List Nat) :=
  [stabPU0, stabPU1, stabPU2, stabPU3, stabPU4, stabPU5, stabPU6, stabPU7, stabPU8, stabPU9,
    stabPU10, stabPU11, stabPU12, stabPU13, stabPU14, stabPU15, stabPU16, stabPU17, stabPU18,
    stabPU19, stabPU20, stabPU21, stabPU22, stabPU23, stabPU24, stabPU25, stabPU26, stabPU27,
    stabPU28, stabPU29]

@[expose] noncomputable def blkK (u b : Nat) (R BR I S : List Nat) (i : Nat) : Bool :=
  andB (eqLN (fstsK (levels2K u 4 (takeK b (dropK (Nat.mul b i) (lev3K u))))) S)
    (allL S fun s => andB (andB (validK u s) (sgnK u s))
      (elemT u (rtK R BR) I (tabK s) (bOfK u s)))

@[expose] noncomputable def okL (i : Nat) : Bool :=
  blkK 0 8 (repP false) (brP false) (fstIK (invD false)) (getLL partsL i) i

@[expose] noncomputable def okU (i : Nat) : Bool :=
  blkK 1 4 (repP true) (brP true) (fstIK (invD true)) (getLL partsU i) i

@[expose] noncomputable def okUs (j i : Nat) : Bool := okU (Nat.add (Nat.mul 10 j) i)

@[expose] noncomputable def certLetK (CD : List (List (List Nat) × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => andB (allLL c.1 fun x => allL x fun a => Nat.blt a 4) ih) CD

@[expose] noncomputable def repOK (u : Nat) (R BR KR S : List Nat) (D : List (Nat × List Nat × Nat))
    (CD : List (List (List Nat) × Nat × Nat)) (nR nS nV : Nat) : Bool :=
  andB (sortedK S) (andB (nodupK (headK R)) (andB (badK u R) (andB (invsK u R BR)
    (andB (conjsK KR D) (andB (certsK u KR CD) (andB (certLetK CD)
    (andB (Nat.beq (lenK R) nR) (andB (Nat.beq (lenK S) nS) (andB (isNilK (dropK nV (lev3K u)))
    (allL R fun s => andB (validK u s) (sgnK u s)))))))))))

end CFSG.KC.Misc.Oq

end
