
module

public import CFSG.Sporadic.ThSchreier.PlaneFactsBase1
import all CFSG.Sporadic.ThSchreier.PlaneFactsBase
import all CFSG.Sporadic.ThSchreier.PlaneFactsBase1

public import CFSG.Sporadic.ThSchreier.GlobalIndex
public import Certificates.Certificate2317
public import CFSG.Sporadic.ThSchreier.CentralizerDataInputs
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.Simple
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbit
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public meta import CFSG.Sporadic.ThSchreier.Words
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.ThSchreier.Transporter
public import CFSG.Sporadic.ThSchreier.UASpace

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise


theorem rowPlane_subset_planeUA_iff (k : Key) :
    rowPlane k ⊆ (planeUA : Set RowV) ↔ inUA k.u = true ∧ inUA k.v = true := by
  rw [rowPlane_eq_span, inUA_iff, inUA_iff, SetLike.coe_subset_coe, Submodule.span_le,
    Set.insert_subset_iff, Set.singleton_subset_iff]
  rfl

section Facts

variable (hF : OrbitFacts) (hS : ThScanFacts)
include hF hS

theorem iota_eq_rowPlane (i : Fin nPlanes) :
    iota i = rowPlane (rowKeyOf (readKey thSt.keys i)) := by
  rw [iota_eq_colPlane hF hS, colPlane, psiSet, rowPlane_rowKeyOf]

theorem a_smul_iota_iff (i : Fin nPlanes) : a • iota i = iota i ↔ αIdx i = i := by
  rw [← iota_phi, iota_injective.eq_iff, Fin.ext_iff]
  show (alphaPerm i : ℕ) = i ↔ _
  rw [alphaPerm_val hF hS]

theorem a_smul_iota_iff_mem (i : Fin nPlanes) : a • iota i = iota i ↔ i.val ∈ centFixedIdx := by
  rw [a_smul_iota_iff hF hS, fixed_iff_mem hS (nPlanes_eq_nX hF hS ▸ i.isLt)]

theorem iota_mem_planeY_iff (i : Fin nPlanes) : iota i ∈ planeY ↔ i.val ∈ centImageIdx := by
  have hi : i.val < nX := nPlanes_eq_nX hF hS ▸ i.isLt
  constructor
  · rintro ⟨-, hsub⟩
    have hfix : a • iota i = iota i := a_smul_plane_of_subset hsub
    have hmem := (a_smul_iota_iff_mem hF hS i).1 hfix
    obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hmem
    have h := ScanFacts.fixedImage hS k (by simpa [centFixedArr] using hk)
    rw [show centFixedArr[k]! = centFixedIdx[k] from getElem!_toArray_eq hk, hke] at h
    rw [iota_eq_rowPlane hF hS, rowPlane_subset_planeUA_iff] at hsub
    have h' : inUAT (frTable rowsUAQ)
          (imageKey (frTable (transposeRows fcRows)) (readKey (thBFS ()).keys i)).u = true ∧
        inUAT (frTable rowsUAQ)
          (imageKey (frTable (transposeRows fcRows)) (readKey (thBFS ()).keys i)).v = true := hsub
    rw [h'.1, h'.2, Bool.true_and, eq_comm, Array.contains_iff_mem] at h
    simpa [centImageArr] using h
  · intro hmem
    obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hmem
    obtain ⟨-, hkey, hu, hv⟩ := centImage_mem hS hk
    refine ⟨iota_mem i, ?_⟩
    rw [iota_eq_rowPlane hF hS, ← hke, hkey, rowPlane_subset_planeUA_iff]
    exact ⟨hu, hv⟩

theorem canonRows_image {k : ℕ} (hk : k < 120) :
    ∃ h : centImageIdx[k]'(by rw [centImage_length]; exact hk) < nPlanes,
      CanonRows (iota ⟨_, h⟩) (centImageRows.getD (2 * k) 0)
        (centImageRows.getD (2 * k + 1) 0) := by
  have hk' : k < centImageIdx.length := by rw [centImage_length]; exact hk
  obtain ⟨hlt, hkey, -, -⟩ := centImage_mem hS hk'
  have hlt' : centImageIdx[k] < nPlanes := nPlanes_eq_nX hF hS ▸ hlt
  refine ⟨hlt', ?_⟩
  have hr1 : centImageRows.getD (2 * k) 0 < 2 ^ 248 := by
    rw [List.getD_eq_getElem _ _ (by rw [centImageRows_length]; omega)]
    exact centImageRows_lt _ (List.getElem_mem _)
  have hr2 : centImageRows.getD (2 * k + 1) 0 < 2 ^ 248 := by
    rw [List.getD_eq_getElem _ _ (by rw [centImageRows_length]; omega)]
    exact centImageRows_lt _ (List.getElem_mem _)
  have hc := canonRows_of_isCanonical (rowKeyOf_canonical hF hlt)
  have hu : (rowKeyOf (readKey thSt.keys centImageIdx[k])).u.toNat =
      centImageRows.getD (2 * k) 0 := by
    rw [hkey, centImageKeys_getElem hk, v4OfNat_toNat_of_lt hr1]
  have hv : (rowKeyOf (readKey thSt.keys centImageIdx[k])).v.toNat =
      centImageRows.getD (2 * k + 1) 0 := by
    rw [hkey, centImageKeys_getElem hk, v4OfNat_toNat_of_lt hr2]
  rw [hu, hv] at hc
  rw [iota_eq_rowPlane hF hS]
  exact hc

theorem ncard_fixed : {P | P ∈ planeX ∧ a • P = P}.ncard = 10200 := by
  have he : {P | P ∈ planeX ∧ a • P = P} = iota '' {i : Fin nPlanes | i.val ∈ centFixedIdx} := by
    ext P
    constructor
    · rintro ⟨hP, hfix⟩
      obtain ⟨i, rfl⟩ := iota_surjective hP
      exact ⟨i, (a_smul_iota_iff_mem hF hS i).1 hfix, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨iota_mem i, (a_smul_iota_iff_mem hF hS i).2 hi⟩
  rw [he, Set.ncard_image_of_injective _ iota_injective,
    ncard_fin_mem (centFixed_sorted hS).nodup fun x hx =>
      nPlanes_eq_nX hF hS ▸ (centFixed_mem hS hx).1, centFixed_length]

theorem ncard_planeY : planeY.ncard = 120 := by
  have he : planeY = iota '' {i : Fin nPlanes | i.val ∈ centImageIdx} := by
    ext P
    constructor
    · intro hP
      obtain ⟨i, rfl⟩ := iota_surjective hP.1
      exact ⟨i, (iota_mem_planeY_iff hF hS i).1 hP, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact (iota_mem_planeY_iff hF hS i).2 hi
  rw [he, Set.ncard_image_of_injective _ iota_injective,
    ncard_fin_mem (centImage_sorted hS).nodup fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      exact nPlanes_eq_nX hF hS ▸ (centImage_mem hS hk).1, centImage_length]

theorem planeStar_eq_iota :
    ∃ h : 120754 < nPlanes, planeStar = iota ⟨120754, h⟩ ∧ iota ⟨120754, h⟩ ∈ planeY := by
  obtain ⟨hlt, hkey⟩ := ScanFacts.star hS
  have hlt' : 120754 < nPlanes := nPlanes_eq_nX hF hS ▸ hlt
  refine ⟨hlt', ?_, (iota_mem_planeY_iff hF hS _).2 native_star_mem⟩
  rw [iota_eq_rowPlane hF hS, planeStar_eq_rowPlane]
  exact congrArg rowPlane hkey.symm

end Facts

end CFSG.Sporadic.ThSchreier
