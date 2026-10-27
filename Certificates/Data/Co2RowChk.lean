module

public import CFSG.Sporadic.Co2I301.Inputs
public import CFSG.Sporadic.Co2Schreier.QCheckInputs
public meta import CFSG.Sporadic.Co2I301.Inputs
public meta import CFSG.Sporadic.Co2Schreier.QCheckInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.Co2RowNative

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Co2Cert
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.I271.Co2Cent CFSG.Sporadic.Schreier.Co3.Native
  CFSG.Sporadic.Co2I301 CFSG.Sporadic.Co2Schreier CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

@[expose] def co2K1Cols : Array ℕ := #[215, 212, 166, 62, 103, 35, 150, 85]

@[expose] def co2K2Cols : Array ℕ := #[98, 96, 5, 54, 74, 141, 88, 118]

@[expose] def co2DCols : Array ℕ := #[56, 153, 21, 96, 60, 101, 13, 255]

@[expose] def leafD3 (D a : Array ℕ) : Bool :=
  !(eqA 63 (compA 63 a (compA 63 a a)) (idA 63)) || eqA 63 a (idA 63) || eqA 63 a D ||
    eqA 63 a (compA 63 D D)

@[expose] def sixX0Check (_ : Unit := ()) : Bool :=
  let K1 := i301K1 (); let K2 := i301K2 (); let D := i301D ()
  let X0 := compA 63 (perm63Of K1) (perm63Of K2)
  let D63 := perm63Of D
  eqA 2300 (powArr 2300 (compA 2300 K1 K2) 5) (idA 2300) &&
    caseChainOK2P 63 sixRec.strongArrs sixRec.baseArr sixRec.wordArrs sixRec.origArrs[0]!
      sixRec.origArrs[1]! &&
    centNormMemOKP 5 63 sixRec.strongArrs sixRec.baseArr X0 [] #[] (fun _ => true) (leafD3 D63)

@[expose] def spanStepL (Ts : List (Array ℕ)) (S : ℕ) : ℕ :=
  (List.range 256).foldl (fun acc a =>
    if S.testBit a then Ts.foldl (fun acc' T => spanIns acc' (vecMulN 8 T a)) acc else acc) S

@[expose] def spanIterL (Ts : List (Array ℕ)) : ℕ → ℕ → ℕ
  | 0, S => S
  | n + 1, S => spanIterL Ts n (spanStepL Ts S)

@[expose] def conjColsOK (g cols : Array ℕ) : Bool :=
  validA 2300 g && isInvA 2300 g (invCand 2300 g) &&
    allLt 8 fun l => decide (cols[l]! < 256) &&
      isProdOrZ (compA 2300 (compA 2300 g qArrs[l]!) (invCand 2300 g)) cols[l]!

@[expose] def v8Check (_ : Unit := ()) : Bool :=
  conjColsOK (i301K1 ()) co2K1Cols && conjColsOK (i301K2 ()) co2K2Cols &&
    conjColsOK (i301D ()) co2DCols &&
    allLt 255 fun v =>
      spanIterL [co2K1Cols, co2K2Cols, co2DCols] 5 (spanIns 1 (v + 1)) == 2 ^ 256 - 1

@[expose] def co2RowCheck (_ : Unit := ()) : Bool := sixX0Check () && v8Check ()

end CFSG.LocalAnalysis.GLTheoremA.H301B.Co2RowNative
