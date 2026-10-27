module

public import Certificates.Data.U43Model

public section

namespace Certificates.Asc82Swap

open CFSG.Monster.B.Co2.Native CFSG.KGroups.Native CFSG.KGroups.U43

@[expose] def elemList (n : Nat) (tA tB : Array Nat) : Array (Array Nat) :=
  (bfsRec (leftStep n (hGens n tA tB)) 4 1200 (idA n)).L

@[expose] def isOddA (n : Nat) (t : Array Nat) : Bool := eqA n (powA n t 9) (idA n)

@[expose] def oddList (n : Nat) (L : Array (Array Nat)) : Array (Array Nat) :=
  L.filter (isOddA n)

@[expose] def oddNe (n : Nat) (O : Array (Array Nat)) (one : Array Nat) : Array (Array Nat) :=
  O.filter fun t => !eqA n t one

@[expose] def commB (n : Nat) (t u : Array Nat) : Bool := eqA n (compA n t u) (compA n u t)

@[expose] def conjArr (n : Nat) (O Oi : Array (Array Nat)) (g : Array Nat) : Array (Array Nat) :=
  (Array.range O.size).map fun k => compA n O[k]! (compA n g Oi[k]!)

@[expose] def cenB (n : Nat) (cg : Array (Array Nat)) (h : Array Nat) : Bool :=
  cg.all fun c => commB n h c

@[expose] def t1Check (n : Nat) (L cg₁ cg₂ : Array (Array Nat)) (one xA : Array Nat) : Bool :=
  allLt L.size fun j =>
    !(cenB n cg₁ L[j]! && cenB n cg₂ L[j]!) || eqA n L[j]! one || eqA n L[j]! xA

@[expose] def t2Check (n : Nat) (L Li X1 X2 cg₁ cg₂ : Array (Array Nat)) : Bool :=
  Nat.any L.size fun kc _ =>
    X1.all (fun o => cenB n cg₁ (compA n Li[kc]! (compA n o L[kc]!))) &&
      X2.all (fun o => cenB n cg₂ (compA n L[kc]! (compA n o Li[kc]!)))

@[expose] def swapTAux (n : Nat) (L Li O O1 : Array (Array Nat))
    (CT : Array (Array (Array Nat))) (one xA : Array Nat) : Bool :=
  allLt O1.size fun a => allLt O1.size fun b =>
    !(cenB n CT[b]! O1[a]! && cenB n CT[a]! O1[b]!) ||
      (t1Check n L CT[a]! CT[b]! one xA &&
        t2Check n L Li (O.filter (cenB n CT[b]!)) (O.filter (cenB n CT[a]!)) CT[a]! CT[b]!)

@[expose] def swapTCheck (n : Nat) (tA tB : Array Nat) : Bool :=
  let L := elemList n tA tB
  let Li := invArrs n L
  let O := oddList n L
  let Oi := invArrs n O
  let one := idA n
  let O1 := oddNe n O one
  let CT := O1.map (conjArr n O Oi)
  invsOK n L Li && invsOK n O Oi && eqA n (compA n tA tA) one && swapTAux n L Li O O1 CT one tA

@[expose] def oddCentAux (n : Nat) (L O1 : Array (Array Nat)) : Bool :=
  allLt O1.size fun a => (L.filter fun h => commB n O1[a]! h).size % 16 != 0

@[expose] def oddCentCheck (n : Nat) (tA tB : Array Nat) : Bool :=
  let L := elemList n tA tB
  let O := oddList n L
  let one := idA n
  let O1 := oddNe n O one
  oddCentAux n L O1

end Certificates.Asc82Swap
