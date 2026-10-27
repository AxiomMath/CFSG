module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3M12

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover

set_option compiler.extract_closed false

structure GenDatum where
  sw : List ℤ
  xw : List ℤ
  aw : List ℤ
  bw : List ℤ

@[expose] def gen1Data : List GenDatum :=
  [⟨[4], [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2], [1],
      [2, 5, -3, 5, -3, 5, -2, 4]⟩,
    ⟨[2, 4, -3], [-2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2], [1],
      [2, 5, 4, -2, 4, -5, 4, 2]⟩,
    ⟨[2, 4, 2, 4], [2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2], [1],
      [3, 3, -5, -2, 5, 3, 4]⟩]

@[expose] def gen2Data : List GenDatum :=
  [⟨[-2, 3], [1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2], [1, 2, -1, 4, -2, -2],
      [-1, 4, -2, 1, -4, -3, 4, 2]⟩,
    ⟨[1, 2], [1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2], [4, -2, 1, 1, -4, 3, 4],
      [2, -4, 1, -3, -3, 4, -2]⟩,
    ⟨[1, 3], [1], [4], [4, -2, 3, 3, 4, 1, 4]⟩,
    ⟨[-2, -2, 3, 3], [2, 1, -2], [1, 4, 2, 2, 1, 1], [4, 1, 4, 2, 2, 2, 4]⟩]

@[expose] def genOK (gs : List (Equiv.Perm (Fin 12))) (d : GenDatum) : Bool :=
  let x := evalCodes [m12gA, m12gB] d.xw
  commT 12 (toTable x) (toTable (evalCodes gs d.sw)) &&
    tblEq 12 (toTable (evalCodes (gs ++ [x]) d.aw)) (toTable m12gA) &&
    tblEq 12 (toTable (evalCodes (gs ++ [x]) d.bw)) (toTable m12gB)

@[expose] def coverReps (gs : List (Equiv.Perm (Fin 12))) (r : Equiv.Perm (Fin 12))
    (D : List GenDatum) : List (Equiv.Perm (Fin 12)) :=
  r :: D.map fun d => evalCodes gs d.sw

@[expose] def coverOK (gs : List (Equiv.Perm (Fin 12))) (Q : RawSchreierDatum 12)
    (r : Equiv.Perm (Fin 12)) (D : List GenDatum) : Bool :=
  repsOK 12 (listTables gs) (listTables (gs.map (·⁻¹))) (cosetOrderTables Q 1 2)
      ((coverReps gs r D).map toTable) 1000 &&
    D.all fun d => ordTest 12 2 (toTable (evalCodes gs d.sw))

@[expose] def chkCover1 (_ : Unit := ()) : Bool :=
  coverOK k1Gens m12CentQ1 (m12InvReps.getD 0 1) gen1Data

@[expose] def chkGen1 (_ : Unit := ()) : Bool := gen1Data.all (genOK k1Gens)

@[expose] def chkCover2 (_ : Unit := ()) : Bool :=
  coverOK k3Gens m12CentQ2 (m12InvReps.getD 1 1) gen2Data

@[expose] def chkGen2 (_ : Unit := ()) : Bool := gen2Data.all (genOK k3Gens)

end CFSG.ClassicalInvolution.Q3.TL4.E3S3M12
