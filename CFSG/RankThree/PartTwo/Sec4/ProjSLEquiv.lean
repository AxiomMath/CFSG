module

public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.Assembly.LowTwoRank

@[expose] noncomputable def projSLEquivPSL (F : Type) [Field F] :
    CFSG.Assembly.RankThreeEven.projSL 2 F ≃* ProjectiveSpecialLinearGroup (Fin 2) F :=
  (MulEquiv.subgroupCongr (show CFSG.Assembly.RankThreeEven.projSL 2 F =
      (StatedSL 2 F).map (ProjGenLinGroup.mk : GL (Fin 2) F →* _) by
    have h : {A : GL (Fin 2) F | (A : Matrix (Fin 2) (Fin 2) F).det = 1} =
        ((GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker : Set (GL (Fin 2) F)) := by
      ext A
      simp [Units.ext_iff]
    rw [StatedSL, h, Subgroup.closure_eq]
    rfl)).trans
    ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (StatedSL 2 F)).symm.trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm)

end CFSG.RankThree.PartTwo.Sec4
