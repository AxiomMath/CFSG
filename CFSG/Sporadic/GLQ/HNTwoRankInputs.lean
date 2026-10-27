module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.MatrixSeedIdentification
import CFSG.Blueprint.NativeSporadic
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public noncomputable section

namespace CFSG.Sporadic.GLQ

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
open scoped Matrix

namespace HNTwoRank

@[expose] def hnProg : List Instr := [
    .mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 5 8, .mu 3 8 9, .mu 9 4 10, .mu 10 10 9,
    .mu 10 9 8, .mu 9 8 2]

@[expose] def hnWords : Fin 5 → List ℤ := ![
  [-2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2],
  [1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2,
    1, 2],
  [2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, -2],
  [1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2],
  [1, -2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1]]

@[expose] def hnRegs : Array (Array (Array ℕ) × Array (Array ℕ)) :=
  runProgN (opsP 5 133) (initRegsN (opsP 5 133) 11
    ((opsP 5 133).decode NativeSporadic.HNSeed1, (opsP 5 133).decode NativeSporadic.HNSeed1)
    ((opsP 5 133).decode NativeSporadic.HNSeed2,
      (opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed2) 2)) hnProg

@[expose] def hnCheck : Bool :=
  hnProg.all (Instr.lt 11) && elem2OK (opsP 5 133)
    (List.ofFn fun j => signedWordN (opsP 5 133) hnRegs[1]! hnRegs[2]! (hnWords j)) [0]

end HNTwoRank

open HNTwoRank

end CFSG.Sporadic.GLQ
