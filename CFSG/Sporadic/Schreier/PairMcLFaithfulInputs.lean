module

public import CFSG.Sporadic.Schreier.PairMcLCert
public import CFSG.Sporadic.Schreier.PairAction
public import CFSG.Sporadic.McL.Setup
public import CFSG.F3.SepSpec
public import CFSG.Blueprint.MatrixSeedIdentification
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public meta import Certificates.Data.CFSGNative.J1.Vec
public meta import Certificates.Data.CFSGNative.F3.Sep
public meta import Certificates.Data.CFSGNative.McL.Certificate
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate2240

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.J1 CFSG.Sporadic.J1.Native Matrix
  CFSG.F3.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def vOfList (d : ℕ) (v : List ℕ) : V := V.ofFn d fun j => v.getD j 0

@[expose] def mclBasisMatWith (W : Array (List ℕ)) : List (List ℕ) :=
  colMat 21 (mclBasisIdx.map fun i => W[i]!)

@[expose] def mclFaithfulWith (W : Array (List ℕ)) (S : Array (Array ℕ)) (A1 A2 : Array V) :
    Bool :=
  let a0 := S[0]!
  let a1 := S[1]!
  let Cl := mclBasisMatWith W
  allLt 275 (fun i => W[i]!.any (· != 0)) &&
    allLt 275 (fun i => allLt i fun j => W[i]! != W[j]!) &&
    allLt 275 (fun i => (mulVecM 21 A1 (vOfList 21 W[i]!)).beq (vOfList 21 W[a0[i]!]!) &&
      (mulVecM 21 A2 (vOfList 21 W[i]!)).beq (vOfList 21 W[a1[i]!]!)) &&
    CFSG.Sporadic.J1.Native.wfM 21 (gaussInv 3 21 Cl) && mulL 3 21 (gaussInv 3 21 Cl) Cl == idL 21

end CFSG.Sporadic.Schreier
