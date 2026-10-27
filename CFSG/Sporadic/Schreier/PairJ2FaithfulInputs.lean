
module

public import CFSG.Sporadic.Schreier.PairJ2CertBase
public import CFSG.Sporadic.Schreier.PairAction
public import CFSG.Sporadic.J2.Setup
public import CFSG.Blueprint.MatrixSeedIdentification
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import CFSG.Blueprint.NativeSporadic
public meta import CFSG.Sporadic.Schreier.PairJ2CertBase
public meta import Certificates.Data.CFSGNative.J1.Vec
public meta import Certificates.Data.CFSGNative.J2.Certificate
public import CFSG.Sporadic.Schreier.PairJ2CertInputs

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.J1 CFSG.Sporadic.J1.Native Matrix

@[expose] def j2BasisMat : List (List ℕ) := colMat 14 (j2BasisIdx.map fun i => j2Vectors[i]!)

@[expose] def j2BasisInv : List (List ℕ) := gaussInv 5 14 j2BasisMat

@[expose] def j2FaithfulOK : Bool :=
  allLt 315 (fun i => j2Vectors[i]!.any (· != 0)) &&
    allLt 315 (fun i => allLt i fun j => j2Vectors[i]! != j2Vectors[j]!) &&
    allLt 315 (fun i =>
      mvL 5 CFSG.Sporadic.J2.Native.mA j2Vectors[i]! == j2Vectors[(j2StrongArrs[0]!)[i]!]! &&
      mvL 5 CFSG.Sporadic.J2.Native.mB j2Vectors[i]! == j2Vectors[(j2StrongArrs[1]!)[i]!]!) &&
    wfM 14 j2BasisInv && mulL 5 14 j2BasisInv j2BasisMat == idL 14

end CFSG.Sporadic.Schreier
