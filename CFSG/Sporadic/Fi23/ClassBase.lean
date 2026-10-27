
module

public import CFSG.Sporadic.Fi23.SetupBase

public section

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev letters : Array Table := chainLetters orb

noncomputable abbrev trees : Array CFSG.Perm.Native.Tree :=
  CFSG.Perm.Native.chainTrees 31671 letters chainBase

noncomputable abbrev lv1 : Array ℕ := CFSG.Perm.Native.levelLetters letters chainBase 1

noncomputable abbrev T2 : CFSG.Perm.Native.Tree :=
  CFSG.Perm.Native.treeBFS 31671 subRoot letters lv1

noncomputable abbrev tabY : Table := letters[2]!

noncomputable abbrev tabAY : Table := compT 31671 orb.alpha tabY

end CFSG.Sporadic.Fi23
