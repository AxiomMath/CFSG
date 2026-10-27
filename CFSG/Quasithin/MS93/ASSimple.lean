module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.TrialityD4
public import CFSG.LieType.Simplicity.TitsModel

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin

@[expose] def RankTwoLieSimple : Prop :=
  ∀ (X : Type) [Group X], IsRankTwoLie2Derived X → IsSimpleGroup X

theorem rankTwoLieSimple_holds :
    RankTwoLieSimple := by
  intro X _ h
  rcases h with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨⟨eX⟩⟩ | ⟨e, h⟩ | h | ⟨e, h⟩ | ⟨e, h⟩ | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 e h).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 4 2 e h).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 5 2 e h).2
  · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X 2 2 e h
  · have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact eX.isSimpleGroup
  · exact (CFSG.LieType.Simplicity.fam_g2_simplicity X 2 e h).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 3 1 h).2
  · exact (CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 e h).2
  · exact (CFSG.LieType.Simplicity.fam_2f4_simplicity X 2 e h).2
  · exact (CFSG.LieType.Simplicity.fam_tits_simplicity X 2 1 h).2

end CFSG.Quasithin.MS93
