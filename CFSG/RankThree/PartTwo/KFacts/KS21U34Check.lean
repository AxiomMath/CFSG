module

public import CFSG.GH74.KGroups.FieldGF
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public meta import CFSG.GH74.KGroups.FieldGF
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import CFSG.RankThree.PartTwo.KFacts.KS21U34CheckInputs
public import Certificates.Certificate8167

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.U34

open CFSG.GH74.KGroups Matrix

@[expose] def pre4 (c : GF16) : GF4 :=
  if c = GF16.ofNat' 6 then GF4.ofNat' 2 else if c = GF16.ofNat' 7 then GF4.ofNat' 3
  else if c = GF16.ofNat' 1 then GF4.ofNat' 1 else GF4.ofNat' 0

theorem u34Facts : U34Facts :=
  Certificates.certificate8167

end CFSG.RankThree.PartTwo.KFacts.KS21.U34
