module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksData
public import CFSG.RankThree.Native.ONTripleModelInputs
public import Certificates.Data.Kernel.Misc.F7Fast

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

open CFSG.KC.Misc.F7 CFSG.KC.Loop CFSG.RankThree.Native.ONTriple

@[expose] noncomputable def nPt : Nat := nat_lit 122760

@[expose] noncomputable def ptRec (k : Nat) : Nat :=
  fld(MB.blkSel (Nat.shiftRight k (nat_lit 4)), Nat.mul (nat_lit 1168) (Nat.land k (nat_lit 15)),
    Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1168)) (nat_lit 1))

@[expose] noncomputable def rCode (r : Nat) : Nat :=
  Nat.land r (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1080)) (nat_lit 1))

@[expose] noncomputable def rPw (r : Nat) : Nat := fld(r, nat_lit 1080, nat_lit 281474976710655)
@[expose] noncomputable def rPar (r : Nat) : Nat := fld(r, nat_lit 1128, nat_lit 131071)
@[expose] noncomputable def rLet (r : Nat) : Nat := fld(r, nat_lit 1145, nat_lit 15)
@[expose] noncomputable def rSig (r : Nat) : Nat := fld(r, nat_lit 1149, nat_lit 131071)

@[expose] noncomputable def ptCode (k : Nat) : Nat := rCode (ptRec k)
@[expose] noncomputable def ptPw (k : Nat) : Nat := rPw (ptRec k)

@[expose] noncomputable def orbStart (o : Nat) : Nat :=
  nthN [nat_lit 0, nat_lit 1, nat_lit 58654, nat_lit 110790, nat_lit 116376, nat_lit 122760] o

@[expose] noncomputable def startOf (k : Nat) : Nat :=
  ifN (Nat.blt k (nat_lit 1)) (nat_lit 0) (ifN (Nat.blt k (nat_lit 58654)) (nat_lit 1)
    (ifN (Nat.blt k (nat_lit 110790)) (nat_lit 58654)
      (ifN (Nat.blt k (nat_lit 116376)) (nat_lit 110790) (nat_lit 116376))))

@[expose] noncomputable def letRev (s : Nat) : Nat := MB.lrSel s

@[expose] noncomputable def treeOK (k r V : Nat) : Bool :=
  strictB (rPar r) fun p => strictB (rLet r) fun s =>
    andB (Nat.blt p k) (andB (Nat.blt s (nat_lit 16))
      (andB (ifB (Nat.beq k (startOf k)) true
          (andB (Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 1))
            (andB (Nat.blt s (nat_lit 12)) (Nat.ble (startOf k) p))))
        (inSpan8 (f7Img (ptCode p) (letRev s)) V (rPw r))))

@[expose] noncomputable def ordOK (k : Nat) : Bool :=
  strictB (rSig (ptRec k)) fun a =>
    andB (Nat.blt a nPt) (ifB (Nat.blt (Nat.succ k) nPt)
      (strictB (rSig (ptRec (Nat.succ k))) fun b => Nat.blt (ptCode a) (ptCode b)) true)

@[expose] noncomputable def ptOK (k : Nat) : Bool :=
  strictB (ptRec k) fun r => strictB (rCode r) fun c =>
    andB (f7Canon c (rPw r)) (andB (ordOK k)
      (ifB (Nat.beq k (nat_lit 0)) true (strictB (widenF c) fun V => treeOK k r V)))

@[expose] noncomputable def ptsOK (b n : Nat) : Bool := allN n fun t => ptOK (Nat.add b t)

@[expose] noncomputable def lrOK (s : Nat) : Bool :=
  Nat.beq (letRev s) (revM (ifN (Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 0))
    (genM (Nat.shiftRight s (nat_lit 1))) (genIM (Nat.shiftRight s (nat_lit 1)))))

@[expose] noncomputable def fixesOK (k l : Nat) : Bool :=
  inSpan8 (f7Img (ptCode k) (letRev (Nat.add (Nat.mul (nat_lit 2) l) (nat_lit 1))))
    (widenF (ptCode k)) (ptPw k)

@[expose] noncomputable def fixP (o : Nat) : Nat := nthN MB.fixP o
@[expose] noncomputable def fixL (o : Nat) : Nat := nthN MB.fixL o

@[expose] noncomputable def orbFixOK (o : Nat) : Bool :=
  andB (Nat.ble (orbStart o) (fixP o)) (andB (Nat.blt (fixP o) (orbStart (Nat.succ o)))
    (andB (Nat.blt (fixL o) (nat_lit 6)) (fixesOK (fixP o) (fixL o))))

@[expose] noncomputable def zScalar : Bool := Nat.beq (genM (nat_lit 7)) (Nat.mul (nat_lit 2) idM)

@[expose] noncomputable def detL (k : Nat) : List Nat :=
  nthLN [MB.dL0, MB.dL1, MB.dL2, MB.dL3, MB.dL4, MB.dL5] k
@[expose] noncomputable def detU (k : Nat) : List Nat :=
  nthLN [MB.dU0, MB.dU1, MB.dU2, MB.dU3, MB.dU4, MB.dU5] k
@[expose] noncomputable def detS (k : Nat) : List Nat :=
  nthLN [MB.dS0, MB.dS1, MB.dS2, MB.dS3, MB.dS4, MB.dS5] k

@[expose] noncomputable def swapN (a b i : Nat) : Nat := ifN (Nat.beq i a) b (ifN (Nat.beq i b) a i)

@[expose] noncomputable def prodN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun k acc => Nat.mul acc (f k)) n

@[expose] noncomputable def luOK (U : Nat) (L U' : List Nat) (a b : Nat) : Bool :=
  andB (allN (nat_lit 8) fun i => allN (nat_lit 8) fun j =>
      Nat.beq (Nat.mod (sumN (nat_lit 8) fun m =>
          Nat.mul (nthN L (Nat.add (Nat.mul (nat_lit 8) i) m))
            (nthN U' (Nat.add (Nat.mul (nat_lit 8) m) j))) (nat_lit 7))
        (lane (row U (swapN a b i)) j))
    (andB (allN (nat_lit 8) fun i => allN (nat_lit 8) fun j =>
        ifB (Nat.blt i j) (Nat.beq (nthN L (Nat.add (Nat.mul (nat_lit 8) i) j)) (nat_lit 0))
          (ifB (Nat.beq i j)
            (Nat.beq (Nat.mod (nthN L (Nat.add (Nat.mul (nat_lit 8) i) j)) (nat_lit 7)) (nat_lit 1))
            (Nat.beq (Nat.mod (nthN U' (Nat.add (Nat.mul (nat_lit 8) i) j)) (nat_lit 7))
              (nat_lit 0))))
      (andB (Nat.beq (Nat.mod (prodN (nat_lit 8) fun i =>
            nthN U' (Nat.add (Nat.mul (nat_lit 8) i) i)) (nat_lit 7)) (nat_lit 1))
        (andB (Nat.blt a b) (Nat.blt b (nat_lit 8)))))

@[expose] noncomputable def detOK (k : Nat) : Bool :=
  andB (allN (nat_lit 8) fun c => Nat.beq (pvF (ptPw (nat_lit 0)) c) c)
    (strictB (imgS (widenF (ptCode (nat_lit 0))) (genM k)) fun U =>
      luOK U (detL k) (detU k) (nthN (detS k) (nat_lit 0)) (nthN (detS k) (nat_lit 1)))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
