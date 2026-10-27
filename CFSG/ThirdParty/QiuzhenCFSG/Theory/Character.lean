module  -- shake: keep-all --deprecated_module: ignore

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Orthogonality
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Integrality
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Induction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.BrauerSuzuki
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ConjClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.SimpleCriteria
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Completeness
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.BrauerPermutation
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.CharacterValues
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.DegreeBounds
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Cyclotomic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.CrossCharBrauer

namespace CFSG
end CFSG
open CFSG

/-!
# Character theory core

Clean, self-contained infrastructure for the character theory of finite groups
over `ℂ`: class functions `G → ℂ`, the scalar product, characters and
irreducible characters (via Mathlib representation theory), generalized
characters, orthonormality of irreducible characters, integrality of character
values, induction of class functions, the Brauer--Suzuki pairing machinery,
and the bridge to class functions on conjugacy classes `ConjClasses G → ℂ`.

This module is the aggregator; the content lives in `Theory/Character/*`:
- `ClassFunction` — class functions and the scalar product
- `Orthogonality` — orthonormality of irreducible characters
- `Integrality` — algebraic integrality of character values
- `Induction` — induction of class functions
- `BrauerSuzuki` — the Brauer--Suzuki scalar-product expansion
- `ConjClassFunction` — class functions on conjugacy classes and the bridges
-/
