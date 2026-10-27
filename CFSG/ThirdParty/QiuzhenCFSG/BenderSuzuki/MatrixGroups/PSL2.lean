module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

namespace CFSG
end CFSG
open CFSG

/-!
# Projective special linear matrix groups

This file contains the concrete `PSL(2,F)` matrix-group models used by the
Peterfalvi Part II formalization.  The declarations live in the `BenderSuzuki.MatrixGroups` namespace so matrix-group models are not hidden under a Peterfalvi chapter namespace.
-/

namespace CFSG.BenderSuzuki
namespace MatrixGroups

open scoped MatrixGroups
open PFAppendixIII

universe w

/-- The actual projective special linear matrix group `PSL(2,F)`. -/
public abbrev PSL2MatrixGroup (F : Type w) [Field F] :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) F


/-- The actual projective special linear matrix group over `GF(2^m)`. -/
public abbrev PSL2BinaryMatrixGroup (m : ℕ) :=
  PSL2MatrixGroup (BinaryGaloisField m)

end MatrixGroups
end CFSG.BenderSuzuki
