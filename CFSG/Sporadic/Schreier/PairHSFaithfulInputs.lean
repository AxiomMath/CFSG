module

public import CFSG.Sporadic.Schreier.PairHSCert
public import CFSG.Sporadic.Schreier.PairAction
public import CFSG.Sporadic.Schreier.PairF2Sep
public import CFSG.Sporadic.HS
public import CFSG.Blueprint.MatrixSeedIdentification
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.HS.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate2218
public import CFSG.Sporadic.Th.F2Spec

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.J1 CFSG.Sporadic.J1.Native Matrix
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Schreier.PairF2

@[expose] def bitsOfList (d : ℕ) (v : List ℕ) : ℕ := ofBits d fun j => v.getD j 0 == 1

@[expose] def hsFaithfulWith (V : Array (List ℕ)) (S : Array (Array ℕ)) (A1 A2 : Array ℕ) : Bool :=
  let bits : Array ℕ := V.map (bitsOfList 20)
  let a0 := S[0]!
  let a1 := S[1]!
  let basis : Array ℕ := Array.ofFn (n := 20) fun k => bits[hsBasisIdx.getD k 0]!
  let E := invRowsF2 20 basis
  allLt 3850 (fun i => bits[i]! != 0 && mulVecRows 20 A1 bits[i]! == bits[a0[i]!]! &&
      mulVecRows 20 A2 bits[i]! == bits[a1[i]!]!) &&
    PairNative.strictInc bits.toList.mergeSort &&
    mulRows 20 E basis == idRows 20 && mulRows 20 basis E == idRows 20

end CFSG.Sporadic.Schreier
