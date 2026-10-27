module

public import CFSG.Sporadic.Co2Jc.Words
public import CFSG.Sporadic.Co2Jc.Data.Simple

public section

namespace CFSG.Sporadic.Co2Jc.Native

open CFSG.Sporadic.Co2Jc CFSG.Sporadic.Co2Jc.Data CFSG.Sporadic.Co2Smith.Native

@[expose] def sameAct (w w' : List Nat) (m : Nat) : Bool := wordAct w m == wordAct w' m

@[expose] def sameActBasis (w w' : List Nat) : Bool :=
  (List.range 10).all fun i => sameAct w w' (2 ^ i)

@[expose] def cWord (j : Nat) : List Nat :=
  let p := perfX[j]!
  commD p.1 p.2

@[expose] def perfExp (j : Nat) : List Nat :=
  (perfW[j]!).flatMap fun l => cWord l

@[expose] def uProdWord (s : List Nat) : List Nat := s.flatMap fun i => uD[i]!

@[expose] def ncWord (j : Nat) : List Nat :=
  let p := ncList[j]!
  p.1 ++ uD[p.2]! ++ invD p.1

@[expose] def ncExp (j : Nat) : List Nat := (ncW[j]!).flatMap fun l => ncWord l

@[expose] def gOK (_ : Unit := ()) : Bool :=
  sameActBasis (g1w ++ g1w ++ g1w) [] &&
    sameActBasis (g2w ++ g2w ++ g2w ++ g2w) [] &&
    sameActBasis (List.replicate 12 0) [] &&
    sameActBasis (List.replicate 3 1) [] &&
    wordAct g1w 2 != 2

@[expose] def perfOK (_ : Unit := ()) : Bool :=
  perfX.length == 2 && perfW.length == 2 &&
    perfX.all (fun p => p.1.all (· < 2) && p.2.all (· < 2)) &&
    perfW.all (fun w => w.all (· < 2)) &&
    (List.range 2).all fun j => sameActBasis (dWord (perfExp j)) (dWord [j])

@[expose] def uOK (_ : Unit := ()) : Bool :=
  uD.length == 4 && uD.all (fun w => w.all (· < 2)) &&
    uConjA.length == 4 && uConjAinv.length == 4 &&
    uConjB.length == 4 && uConjBinv.length == 4 &&
    (uConjA ++ uConjAinv ++ uConjB ++ uConjBinv).all (fun s => s.all (· < 4)) &&
    (List.range 4).all (fun i =>
      (List.range 4).all fun j =>
        sameActBasis (dWord (uD[i]! ++ uD[j]!)) (dWord (uD[j]! ++ uD[i]!))) &&
    (List.range 4).all fun i =>
      sameActBasis (dWord (uD[i]! ++ uD[i]!)) [] &&
      wordAct (dWord uD[i]!) 1 == 1 &&
      sameActBasis ([0] ++ dWord uD[i]! ++ List.replicate 11 0)
        (dWord (uProdWord uConjA[i]!)) &&
      sameActBasis (List.replicate 11 0 ++ dWord uD[i]! ++ [0])
        (dWord (uProdWord uConjAinv[i]!)) &&
      sameActBasis ([1] ++ dWord uD[i]! ++ [1, 1]) (dWord (uProdWord uConjB[i]!)) &&
      sameActBasis ([1, 1] ++ dWord uD[i]! ++ [1]) (dWord (uProdWord uConjBinv[i]!))

@[expose] def hOK (_ : Unit := ()) : Bool :=
  hOrb60.length == 60 && hWords60.length == 60 &&
    hOrb16.length == 16 && hWords16.length == 16 &&
    decide hOrb60.Nodup && decide hWords60.Nodup && decide hOrb16.Nodup &&
      decide hWords16.Nodup &&
    hOrb60[0]! == hRep60 && hOrb16.contains hRep16 &&
    hOrb60.all (fun m => decide (m < 1024) && glNJOm.contains m) &&
    hOrb16.all (fun m => decide (m < 1024) && glNJOm.contains m) &&
    hOrb60.all (fun m => !hOrb16.contains m && m != 1) &&
    hOrb16.all (fun m => m != 1) &&
    hOrb60.all (fun m =>
      hOrb60.contains (wordAct [1] m) && hOrb60.contains (wordAct [0, 0] m)) &&
    hOrb16.all (fun m =>
      hOrb16.contains (wordAct [1] m) && hOrb16.contains (wordAct [0, 0] m)) &&
    ((List.range 60).all fun k =>
      wordAct (hExpand (hWords60[k]!)) hRep60 == hOrb60[k]!) &&
    ((List.range 16).all fun k =>
      wordAct (hExpand (hWords16[k]!)) hRep16 == hOrb16[k]!)

@[expose] def fixOK (_ : Unit := ()) : Bool := wordAct [1] 1 == 1 && wordAct [0, 0] 1 == 1

@[expose] def ncOK (_ : Unit := ()) : Bool :=
  ncList.length == 10 && ncW.length == 2 && ncW.all (fun w => w.all (· < 10)) &&
    (ncList.all fun p => p.1.all (· < 2) && p.2 < 4) &&
    (List.range 2).all fun j => sameActBasis (dWord (ncExp j)) (dWord [j])

@[expose] def simpleOK (_ : Unit := ()) : Bool :=
  gOK () && perfOK () && uOK () && hOK () && fixOK () && ncOK ()

end CFSG.Sporadic.Co2Jc.Native
