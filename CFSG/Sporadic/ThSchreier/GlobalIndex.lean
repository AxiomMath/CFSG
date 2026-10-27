
module

public import CFSG.Sporadic.ThSchreier.GlobalIndexBase1

public import CFSG.Sporadic.ThSchreier.GlobalTransport
public import CFSG.Sporadic.ThSchreier.ScanCheck
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.Simple
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbit
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.LySchreier
  Pointwise

section Facts

variable (hF : OrbitFacts) (hS : ThScanFacts)
include hF

include hS

theorem iotaList_eq :
    iotaList = (List.range nX).map colPlane := by
  classical
  rw [iotaList, ncard_planeX_eq hF]
  refine bfsList_eq (colPlane_mono hS) (colPlane_inj hF) (colPlane_img hF) (colPlane_tree hF)
    (colPlane_disc hF hS) hF.pos ?_ (by omega)
  rw [colPlane, planeAt_zero hF, psiSet_W]

theorem nPlanes_eq_nX :
    nPlanes = nX := by
  rw [nPlanes, iotaList_eq hF hS, List.length_map, List.length_range]

theorem iota_eq_colPlane
    (i : Fin nPlanes) : iota i = colPlane i := by
  have h := iotaList_eq hF hS
  rw [iota]
  simp only [h, List.getElem_map, List.getElem_range]

theorem alphaPerm_val
    (i : Fin nPlanes) : (alphaPerm i : ℕ) = αIdx i := by
  have hi : i.val < nX := nPlanes_eq_nX hF hS ▸ i.isLt
  have h1 : iota (alphaPerm i) = a • iota i := iota_phi a i
  rw [iota_eq_colPlane hF hS, iota_eq_colPlane hF hS] at h1
  have h2 := (colPlane_img hF i hi 0 (by show 0 < 2; decide)).2
  rw [colImg_zero] at h2
  have h3 : colPlane (alphaPerm i) = colPlane (αIdx i) := h1.trans h2
  exact colPlane_inj hF _ (nPlanes_eq_nX hF hS ▸ (alphaPerm i).isLt) _ (hF.αlt i hi) h3

theorem betaPerm_val
    (i : Fin nPlanes) : (betaPerm i : ℕ) = βIdx i := by
  have hi : i.val < nX := nPlanes_eq_nX hF hS ▸ i.isLt
  have h1 : iota (betaPerm i) = b • iota i := iota_phi b i
  rw [iota_eq_colPlane hF hS, iota_eq_colPlane hF hS] at h1
  have h2 := (colPlane_img hF i hi 1 (by show 1 < 2; decide)).2
  rw [colImg_one] at h2
  have h3 : colPlane (betaPerm i) = colPlane (βIdx i) := h1.trans h2
  exact colPlane_inj hF _ (nPlanes_eq_nX hF hS ▸ (betaPerm i).isLt) _ (hF.βlt i hi) h3

end Facts

end CFSG.Sporadic.ThSchreier
