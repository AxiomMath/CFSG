module

public import CFSG.LocalAnalysis.StandardType.GGKD2UnitaryPieces1615

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType

theorem unitaryInndiagIsConj_holds : UnitaryInndiagIsConj := by
  intro d n K _ _ h hd _ _ β hβ
  obtain ⟨B, hB⟩ := hβ
  have e : β = (MulAut.congr (InndiagSU.projEquiv h hd)).symm
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h _ B) := by
    rw [hB]
    exact ((MulAut.congr (InndiagSU.projEquiv h hd)).symm_apply_apply β).symm
  rw [e]
  exact InndiagSU.congr_symm_mem h hd B

end CFSG.StandardType.KD2Pieces1615

end
