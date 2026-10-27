module

public import Certificates.Data.Kernel.Mat12P
public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Check

public section

noncomputable section

namespace Certificates.Kernel.HJ12K

open CFSG.KC.Mat12P CFSG.KC.Mat8P CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

@[expose] def unpackA (X : ℕ) : Array ℕ := (unpackQ X).toArray

@[expose] def acQ : ℕ := codeQ hjAc.toList

@[expose] def bcQ : ℕ := codeQ hjBc.toList

@[expose] def jcQ : ℕ := codeQ hjJc.toList

@[expose] def wordQ (w : List ℕ) : ℕ :=
  w.foldl (fun acc l => mulQ acc (if l = 0 then acQ else bcQ)) oneQ

@[expose] def fullM : ℕ := 2 ^ 4096 - 1

@[expose] def lane (j : ℕ) : ℕ := (2 ^ 2 ^ (j + 1) - 2 ^ 2 ^ j) * (fullM / (2 ^ 2 ^ (j + 1) - 1))

@[expose] def laneMask : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | c :: A, j, i => (if c.testBit i then lane j else 0) ^^^ laneMask A (j + 1) i

@[expose] def fixMask (A : List ℕ) : ℕ :=
  (List.range 12).foldl (fun m i => m &&& (fullM ^^^ (laneMask A 0 i ^^^ lane i))) fullM

@[expose] def bitsM (M : ℕ) : List ℕ := (List.range 4096).filter fun v => M.testBit v

@[expose] def fixQ (X : ℕ) : List ℕ := bitsM (fixMask (unpackQ X))

@[expose] def fixCnt (X : ℕ) : ℕ := CFSG.KC.pc4096 (fixMask (unpackQ X))

@[expose] def roundQ (gs fr : List ℕ) (seen : NT ℕ) : List ℕ × NT ℕ :=
  (fr.flatMap fun s => gs.map fun g => mulQ s g).foldl
    (fun acc t => if memP acc.2 t then acc else (t :: acc.1, insP acc.2 t)) ([], seen)

@[expose] def closQ (gs : List ℕ) : ℕ → List ℕ → NT ℕ → List ℕ → List ℕ
  | 0, fr, _, vis => fr ++ vis
  | fuel + 1, fr, seen, vis =>
    let r := roundQ gs fr seen
    if r.1.isEmpty then fr ++ vis else closQ gs fuel r.1 r.2 (fr ++ vis)

@[expose] def enumQ (gs : List ℕ) : List ℕ := closQ gs 100000 [oneQ] (insP (.tip []) oneQ) []

@[expose] def closedQ (gs X : List ℕ) : Bool :=
  let S := ofListP X
  X.all fun x => gs.all fun g => memP S (mulQ x g)

@[expose] def invPQ (c : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x => if Nat.beq (mulQ c x) oneQ then x else invPQ c fuel (mulQ c x)

@[expose] def invQ (c : ℕ) : ℕ := invPQ c 64 oneQ

@[expose] def invOKQ (g r : ℕ) : Bool := Nat.beq (mulQ g r) oneQ && Nat.beq (mulQ r g) oneQ

@[expose] def gensOKQ (gs : List ℕ) : Bool := gs.all fun g => invOKQ g (invQ g)

@[expose] def x7Core (x : ℕ) : Bool :=
  Nat.beq (mulQ (mulQ (mulQ x x) (mulQ x x)) (mulQ (mulQ x x) x)) oneQ && !Nat.beq x oneQ &&
    fixQ x == [0]

@[expose] def x7Q : Bool := x7Core (wordQ hj_x7Word)

@[expose] def p3At (gs X : List ℕ) (J n : ℕ) : Bool :=
  gensOKQ gs && closedQ gs X && nodupP X && Nat.beq X.length n &&
    Nat.beq (mulQ (mulQ J J) J) oneQ &&
    [oneQ, J, mulQ J J].all fun c => X.all fun p =>
      Nat.beq (mulQ c p) oneQ || Nat.ble (fixCnt (mulQ c p)) 256

@[expose] def p3Q : Bool := p3At (hj_p3Words.map wordQ) (enumQ (hj_p3Words.map wordQ)) jcQ 27

end Certificates.Kernel.HJ12K

end

end
