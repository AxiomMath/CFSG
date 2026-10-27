module

public import CFSG.Sporadic.Co1Patterson.GraphTits
public import CFSG.Sporadic.Co1Patterson.AmalgamLocal
public import CFSG.Sporadic.Co1Patterson.AmalgamInputs
public import Certificates.Certificate21157
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2AData
public import CFSG.Sporadic.Co1Block.XFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS CFSG.Open
  CFSG.Sporadic.Co1Patterson.Native CFSG.Monster.B.Recog
open CFSG.Blueprint (NativeSporadic.Co1)

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

theorem amalgam_check : amalgamCheck = true := Certificates.certificate21157

theorem amalgamCheck_parts :
    orbE.c.pts[triRoots.getD 2 0]! = Native.mul iotaARows (repRows 1) ∧
    1 ≤ gensKe.getD 4 0 ∧ gensKe.getD 4 0 ≤ 190 ∧
    Native.mul (Native.mul (gEl (gensKe.getD 4 0)) (wRows (triW.getD 2 0)))
      (gElInv (gensKe.getD 4 0)) = wRows (triW.getD 0 0) := by
  have h := amalgam_check
  unfold amalgamCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem aNC_mem_qOf_wT (j : Fin 3) : aNC ∈ qOf (wT j : NativeSporadic.Co1) :=
  (locTri_spec j).2.2 vA (by simp)

theorem vE_mem_qOf_wT (j : Fin 3) : (vE : NativeSporadic.Co1) ∈ qOf (wT j : NativeSporadic.Co1) :=
  (locTri_spec j).2.2 vE (by simp)

theorem vE_not_mem_qOf_aNC : (vE : NativeSporadic.Co1) ∉ qOf aNC :=
  a2_adj_vA_vE.2.2.2.1

theorem wT_ne_aNC (j : Fin 3) : (wT j : NativeSporadic.Co1) ≠ aNC := by
  intro h
  have := vE_mem_qOf_wT j
  rw [h] at this
  exact vE_not_mem_qOf_aNC this

theorem wT_mem_qOf_aNC (j : Fin 3) : (wT j : NativeSporadic.Co1) ∈ qOf aNC :=
  mem_qOf_symm pattersonCo1Hyp_native (wT j).2 (wT_ne_aNC j) (aNC_mem_qOf_wT j)

theorem orderOf_vt (v : Vt) : orderOf (v : NativeSporadic.Co1) = 2 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 v.2
  rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_aNC]

theorem vE_mem_cent_aNC : (vE : NativeSporadic.Co1) ∈ C[aNC] :=
  mem_centralizer_singleton_iff.2 a2_adj_vA_vE.2.1.symm

theorem vE_mem_cent_wT (j : Fin 3) : (vE : NativeSporadic.Co1) ∈ C[(wT j : NativeSporadic.Co1)] :=
  qOf_le_centralizer _ (vE_mem_qOf_wT j)

theorem wT_mem_cent_aNC (j : Fin 3) : (wT j : NativeSporadic.Co1) ∈ C[aNC] :=
  qOf_le_centralizer _ (wT_mem_qOf_aNC j)

theorem wT_mem_cent_vE (j : Fin 3) : (wT j : NativeSporadic.Co1) ∈ C[(vE : NativeSporadic.Co1)] :=
  mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (vE_mem_cent_wT j)).symm

theorem uT_two_eq : (uT 2 : NativeSporadic.Co1) = aNC * vE := by
  have hk : triRoots.getD 2 0 < orbE.c.pts.size := by rw [size_orbE]; decide
  have h1 := nrep_cV hk
  rw [amalgamCheck_parts.1] at h1
  exact NRep.unique h1 (nrep_aNC.mul (nrep_repV (show 1 < 10 by norm_num)))

theorem coe_smul_eq {g : NativeSporadic.Co1} {x y : Vt} (h : g • x = y) :
    g * (x : NativeSporadic.Co1) * g⁻¹ = y := by
  rw [← coe_smul_conjVert, h]

theorem coe_vA : (vA : NativeSporadic.Co1) = aNC := rfl

theorem tauT_two_conj : tauT 2 ∈ C[(wT 2 : NativeSporadic.Co1)] ∧
    tauT 2 * aNC * (tauT 2)⁻¹ = vE ∧ tauT 2 * vE * (tauT 2)⁻¹ = aNC := by
  obtain ⟨⟨h1, h2, -, h4⟩, -⟩ := locTri_spec 2
  have e1 := coe_smul_eq h1
  have e2 := coe_smul_eq h2
  rw [coe_vA] at e1 e2
  exact ⟨h4, e1, e2⟩

theorem rhoT_two_conj : rhoT 2 ∈ C[(wT 2 : NativeSporadic.Co1)] ∧
    rhoT 2 * aNC * (rhoT 2)⁻¹ = vE ∧ rhoT 2 * vE * (rhoT 2)⁻¹ = aNC * vE := by
  obtain ⟨-, ⟨h1, h2, -, h4⟩, -⟩ := locTri_spec 2
  have e1 := coe_smul_eq h1
  have e2 := coe_smul_eq h2
  rw [coe_vA] at e1
  rw [uT_two_eq] at e2
  exact ⟨h4, e1, e2⟩

@[expose] noncomputable def kZero : NativeSporadic.Co1 := gElt (gensKe.getD 4 0)

theorem kZero_mem : kZero ∈ C[aNC] ⊓ C[(vE : NativeSporadic.Co1)] := by
  obtain ⟨-, -, -, hcent, -⟩ := triCheck_parts
  have := mem_of_centOK hcent (fun l hl => nrep_gensArr dagOK_true _ hl)
    (nrep_repV (show 1 < 10 by norm_num)) 4 (by rw [gensArr_size]; decide)
  exact this

theorem nrep_wT (j : Fin 3) : NRep (wRows (triW.getD j 0)) (wT j : NativeSporadic.Co1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hloc⟩ := triCheck_parts
  have h := hloc j j.2
  unfold locTriOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hw⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ :=
    h
  have hp := crep_wP hw
  exact nrep_vtxR hp.1 hp.2.1

theorem kZero_conj :
    kZero * (wT 2 : NativeSporadic.Co1) * kZero⁻¹ = (wT 0 : NativeSporadic.Co1) := by
  obtain ⟨-, h1, h2, h3⟩ := amalgamCheck_parts
  have hk := nrep_gEl (dagOK_parts dagOK_true).1 (gensKe.getD 4 0)
  have hki := nrep_gElInv dagOK_true h1 h2
  have hw2 : NRep (wRows (triW.getD 2 0)) (wT 2 : NativeSporadic.Co1) := nrep_wT 2
  have hw0 : NRep (wRows (triW.getD 0 0)) (wT 0 : NativeSporadic.Co1) := nrep_wT 0
  refine NRep.unique ((hk.mul hw2).mul hki) ?_
  rw [h3]
  exact hw0

end CFSG.Sporadic.Co1Patterson
