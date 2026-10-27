
module

public import CFSG.Sporadic.ThSchreier.TransporterBase

public import CFSG.Sporadic.ThSchreier.CentralizerData
public import CFSG.Sporadic.ThSchreier.Words

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

theorem isRows_rowsV :
    IsRows rowsV transporterV := isRows_abRows transporterWord

theorem isRows_rowsVInv :
    IsRows rowsVInv transporterV⁻¹ := by
  have h := isRows_abRows (invWord transporterWord)
  rw [wordG_invWord a b transporterWord transporterWord_letters] at h
  exact h

theorem planeStar_eq_rowPlane :
    planeStar = rowPlane starKey := by
  rw [planeStar, starKey, rowPlane_imageKey isRows_rowsVInv, rowPlane_wKeyRow]

end CFSG.Sporadic.ThSchreier
