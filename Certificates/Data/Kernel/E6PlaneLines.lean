module

public import Certificates.Data.E6ShapeKernel

public section

namespace CFSG.KC.E6PlaneLines

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6ShapeKernel

@[expose] def addL (a b : List ℕ) (k : ℕ) : List ℕ :=
  List.zipWith (fun x y => (x + k * y) % 3) a b

@[expose] def idx3 (l : List ℕ) : ℕ := l.foldr (fun d acc => d + 3 * acc) 0

@[expose] def nsMask : ℕ :=
  1211869148236232539389084061536051648796023896632919327840123577664820522463412604862842937381397715068460242499094924829748342276495488175400064839800588189888854270675913034324227936608086432826121498129358692437385214

@[expose] def nsBit (mask : ℕ) (l : List ℕ) : Bool := mask.testBit (idx3 l)

@[expose] def linesTest (mask : ℕ) (a b : List ℕ) : Bool :=
  decide (2 ≤ ([nsBit mask a, nsBit mask b, nsBit mask (addL a b 1),
    nsBit mask (addL a b 2)].filter id).length)

@[expose] def linesCheckWith (reps : List (List ℕ)) (mask thr : ℕ) : Bool :=
  let T := RootTables.ofCert e6Certificate
  reps.all fun a => (List.range 729).all fun code =>
    let b := digits3 .E6 code
    linesTest mask a b || !(independent a b && decide (thr < kernelCount T a b))

@[expose] def nsAux (mask : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, e :: es =>
    (mask.testBit i == (decide (1 ≤ entryRep e) && decide (entryRep e ≤ 5))) &&
      nsAux mask (i + 1) es

@[expose] def nsMaskCheckWith (mask : ℕ) : Bool := nsAux mask 0 e6ThreeOrbit

@[expose] def nsMaskCheck (_ : Unit := ()) : Bool := nsMaskCheckWith nsMask

@[expose] def passOneCheckWith (rs : List ℕ) : Bool :=
  rs.all fun ρ =>
    (e6ThreeStabs.getD ρ ⟨[], [], []⟩).passing e6Certificate == [List.range Tag.E6.rank]

@[expose] def passOneCheck (_ : Unit := ()) : Bool := passOneCheckWith [1, 2, 3, 4, 5]

end CFSG.KC.E6PlaneLines
