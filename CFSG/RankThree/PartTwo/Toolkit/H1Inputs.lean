module

public import CFSG.RankThree.PartTwo.Toolkit.Statements
public import CFSG.RankThree.PartTwo.Toolkit.Cocycle
public meta import CFSG.RankThree.PartTwo.Toolkit.Raw
public meta import CFSG.RankThree.PartTwo.Toolkit.Cocycle
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Raw Subgroup

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "SL33" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)

@[expose] def slA : SL33 := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def slB : SL33 := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩

end CFSG.RankThree.PartTwo.Toolkit
