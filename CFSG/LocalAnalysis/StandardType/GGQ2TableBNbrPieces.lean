module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrUnit
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrPlaneZero
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrPlaneExt
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrExc
public import CFSG.LocalAnalysis.StandardType.GGQ2NoTwoNodeExc
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSmall
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalPlacementHolds

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly

theorem nbrWeylData_plane (k : PlaneRaw.PlaneKind) (t : ℕ) : NbrWeylData (planeEntry k t) := by
  intro v c _ hadm _ hcod
  cases c with
  | zero S => exact planeZero_codeWeylDatum k t S hadm hcod
  | extension e => exact planeExt_codeWeylDatum k t e hadm hcod

theorem nbrWeylData_catalogue (kind : FrameKind) :
    NbrWeylData (catalogueOf classicalCatalogue excCatalogue kind) := by
  cases kind with
  | lin t ε =>
    rw [catalogueOf_classical _ _ (k := .lin t ε) trivial]
    exact nbrWeylData_plane (.linear ε) t
  | symp t =>
    rw [catalogueOf_classical _ _ (k := .symp t) trivial]
    exact nbrWeylData_plane .symplectic t
  | orth t δ =>
    rw [catalogueOf_classical _ _ (k := .orth t δ) trivial]
    exact nbrWeylData_plane (.orthogonal δ) t
  | unitFull N =>
    rw [catalogueOf_classical _ _ (k := .unitFull N) trivial]
    exact nbrWeylData_unitFull N
  | unitHeart N =>
    rw [catalogueOf_classical _ _ (k := .unitHeart N) trivial]
    exact nbrWeylData_unitHeart N
  | exceptional m =>
    rw [catalogueOf_exceptional _ _ (k := .exceptional m) fun h => h]
    exact ExcRaw.nbrWeylData_excRaw m

section


theorem ggQ2TableBNbr_of_excPlacement
    (hplEx : PlacementInputOn ExceptionalLabel (catalogueOf classicalCatalogue excCatalogue)) :
    GGQ2TableBNbr :=
  ggQ2TableBNbr_of_placement
    (placementInput_of_split _ (placementInputOn_classical_holds excCatalogue) hplEx
      (placementInputOn_small _))
    fun kind => tableBNbrAtFrame_of_nbrWeylData (nbrWeylData_catalogue kind)

end

end CFSG.StandardType.GGQ2Frame

end
