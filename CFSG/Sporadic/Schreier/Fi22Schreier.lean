module

public import CFSG.Monster.B.Fischer.Fi22Model
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound

public section

namespace CFSG.Sporadic.Schreier.Fi22

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Monster.B.Fischer

theorem fi22P_outer_solvable :
    Group.IsSolvable (Outer fi22P) := by
  obtain ⟨e⟩ := CTUC_Fi22_full_automorphism_permutation_model.2.2.2.2.2.2.2
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem AT_Fi22_Schreier :
    Group.IsSolvable (Outer Blueprint.NativeSporadic.Fi22) :=
  (@CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism Blueprint.NativeSporadic.Fi22 fi22P
    Units.instGroup _ fi22PermEquiv).2.2 fi22P_outer_solvable

end CFSG.Sporadic.Schreier.Fi22
