module

public import Certificates.Data.OmegaB0
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K442002A
import Certificates.Kernel.PermCent.K442002B
import Certificates.Kernel.PermCent.K442002C
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Sporadic.Schreier
  CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.B0T Certificates.OmegaB0

namespace Certificates

local notation "P45" => Equiv.Perm (Fin 45)

private theorem cOf_one : cOf (1 : P45) = 1 := ev_injective (by rw [ev_cOf, ev_one])

private theorem map_cOf_ev (L : List P45) : (L.map cOf).map ev = L := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun σ _ => ev_cOf σ

private theorem cOf_prod (L : List P45) : cOf L.prod = (L.map cOf).prod := by
  apply ev_injective
  rw [ev_cOf]
  change L.prod = evHom 45 (L.map cOf).prod
  rw [map_list_prod, List.map_map]
  conv_lhs => rw [← List.map_id L]
  exact congrArg List.prod (List.map_congr_left fun σ _ => (ev_cOf σ).symm)

private theorem getD_cOf (B : List P45) (j : Nat) : (B.map cOf).getD j 1 = cOf (B.getD j 1) := by
  rw [← cOf_one, List.getD_map]

private theorem phiTable_map (B : List P45) : (phiTable B).toList.map cOf = phiC (B.map cOf) := by
  unfold phiTable phiC
  rw [List.toList_toArray, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, tab_eq, cOf_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  split
  · exact (getD_cOf B j).symm
  · exact cOf_one

private theorem phi0_ev (Φ : Array P45) (v : Fin 5 → ZMod 2) :
    phi0 Φ v = ev (phi0C (Φ.toList.map cOf) v) := by
  unfold phi0 phi0C
  rw [← cOf_one, List.getD_map, ev_cOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]

private theorem bElems_ev (Φ : Array P45) (allV : List (Fin 5 → ZMod 2)) :
    bElems Φ allV = (bElemsC (Φ.toList.map cOf) allV).map ev := by
  unfold bElems bElemsC
  rw [List.map_map]
  exact List.map_congr_left fun v _ => phi0_ev Φ v

private theorem closed_ev (B : List (CV 45)) : closedChk (B.map ev) = closedC B := by
  unfold closedChk closedC
  simp only [List.length_map, nodup_map_ev, one_eq_ev, decide_mem_map_ev, List.all_map,
    Function.comp_def, ev_inv', ev_mul', decide_ev_eq]

private theorem sylow_ev (T B : List (CV 45)) : sylowChk (T.map ev) (B.map ev) = sylowC T B := by
  unfold sylowChk sylowC
  simp only [List.length_map, decide_mem_map_ev, List.all_map, List.any_map, List.filter_map,
    Function.comp_def, ev_mul', decide_ev_eq, ne_eq, ev_eq_iff]

private theorem cent_ev (A B : List (CV 45)) : centChk (A.map ev) (B.map ev) = centC A B := by
  unfold centChk centC
  simp only [decide_mem_map_ev, List.all_map, Function.comp_def, ev_mul', decide_ev_eq, comm_fast]

private theorem hom_ev (Φ : Array P45) (allV : List (Fin 5 → ZMod 2)) :
    homChk Φ allV = homC (Φ.toList.map cOf) allV := by
  unfold homChk homC
  simp only [phi0_ev, ev_mul', decide_ev_eq]

private theorem act_ev (L A B : List (CV 45)) (bs : List P45) (Φ : Array P45)
    (allV : List (Fin 5 → ZMod 2)) (S5 : List (Equiv.Perm (Fin 5))) :
    actChk (L.map ev) (A.map ev) bs Φ (B.map ev) allV S5 =
      actC L A (bs.map cOf) (Φ.toList.map cOf) B allV S5 := by
  conv_lhs => rw [← map_cOf_ev bs]
  unfold actChk actC normB normBC conjIdx conjIdxC actEq actEqC
  simp only [decide_mem_map_ev, List.all_map, List.any_map, List.filter_map, List.map_map,
    List.findIdx_map, Function.comp_def, ev_mul', ev_inv', decide_ev_eq, phi0_ev]

private theorem class_ev (L : List (CV 45)) (Φ : Array P45) (allV : List (Fin 5 → ZMod 2)) :
    classChk (L.map ev) Φ allV = classC L (Φ.toList.map cOf) allV := by
  unfold classChk classC
  conv_lhs => rw [eq_ev_cOf (Certificates.P43Twin.tA ()), eq_ev_cOf (Certificates.P43Twin.tB ())]
  simp only [List.any_map, Function.comp_def, phi0_ev, ev_mul', ev_inv', decide_ev_eq, conj_fast]

private theorem bl_eq : bElems (phiTable (bl ())) (allVecs ()) = blC.map ev := by
  rw [bElems_ev, phiTable_map, blC.eq_1, phC.eq_1]

theorem certificate442002 : OmegaB0.check () = true := by
  rw [check.eq_1]
  rw [bl_eq, elemsT_eq_elemsC, elemsT_eq_elemsC, elemsT_eq_elemsC, closed_ev, sylow_ev, cent_ev,
    hom_ev, act_ev, class_ev, phiTable_map, ← phC.eq_1, kClosed, kSylow, kCent, kVec, kHom, kAct,
    kClass]
  rfl

end Certificates
