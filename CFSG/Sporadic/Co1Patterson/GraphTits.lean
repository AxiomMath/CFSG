module

public import CFSG.Sporadic.Co1Patterson.GraphTriangles

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS CFSG.Open
  CFSG.Sporadic.Co1Patterson.Native CFSG.Monster.B.Recog
open CFSG.Blueprint (NativeSporadic.Co1)
open scoped Pointwise

theorem orbOK_orbQ : orbOK brayArr brayInvArr zRows orbQ = true := by
  have := exact_orbQ
  unfold exactOK at this
  simp only [Bool.and_eq_true] at this
  exact this.1.1

theorem exists_hQpt {i : ℕ} (hi : i < orbQ.c.pts.size) :
    ∃ g : NativeSporadic.Co1, NRep orbQ.hs[i]! g ∧ NRep orbQ.his[i]! g⁻¹ := by
  obtain ⟨g, -, h1, h2, -⟩ := orbOK_sound matHom orbOK_orbQ brayNC
    (fun l hl => nrep_brayArr l hl) _ nrep_zRows i hi
  exact ⟨g, h1, h2⟩

@[expose] noncomputable def hQpt (i : ℕ) : NativeSporadic.Co1 :=
  if hi : i < orbQ.c.pts.size then Classical.choose (exists_hQpt hi) else 1

theorem hQpt_spec {i : ℕ} (hi : i < orbQ.c.pts.size) :
    NRep orbQ.hs[i]! (hQpt i) ∧ NRep orbQ.his[i]! (hQpt i)⁻¹ := by
  rw [show hQpt i = Classical.choose (exists_hQpt hi) by simp [hQpt, hi]]
  exact Classical.choose_spec (exists_hQpt hi)

@[expose] noncomputable def wT (j : Fin 3) : Vt := (hQpt (triW.getD j 0) * gElt (repJ 0)) • vA

theorem crep_wP {i : ℕ} (hi : i < orbQ.c.pts.size) :
    CRep (wP i) (hQpt i * gElt (repJ 0)) := by
  obtain ⟨-, -, -, -, -, -, -, hpts, -⟩ := orbOK_parts orbOK_orbQ
  have hv := (dagOK_parts dagOK_true).2 _ (repJ_mem (show 0 < 10 by norm_num)).1
    (repJ_mem (show 0 < 10 by norm_num)).2
  refine ⟨(hQpt_spec hi).1.mul (nrep_repX dagOK_true 0), ?_, validRows_mul (hpts i hi).2.1 hv.1,
    validRows_mul hv.2.1 (hpts i hi).2.2.1⟩
  show NRep (Native.mul (repXi 0) orbQ.his[i]!) (hQpt i * gElt (repJ 0))⁻¹
  rw [_root_.mul_inv_rev]
  exact (nrep_repXi dagOK_true (by norm_num)).mul (hQpt_spec hi).2

@[expose] noncomputable def tauT (j : Fin 3) : NativeSporadic.Co1 := gElt (tauIdx.getD j 0)

@[expose] noncomputable def rhoT (j : Fin 3) : NativeSporadic.Co1 := gElt (rhoIdx.getD j 0)

theorem smul_eq_of_rows {T Ti X Y : Native.Rows} {t : NativeSporadic.Co1} {x y : Vt}
    (hT : NRep T t) (hTi : NRep Ti t⁻¹) (hX : NRep X x) (hY : NRep Y y)
    (h : Native.mul (Native.mul T X) Ti = Y) : t • x = y :=
  Subtype.ext (NRep.unique ((hT.mul hX).mul hTi) (by rw [h]; exact hY))

theorem mem_centralizer_of_rows {T W : Native.Rows} {t w : NativeSporadic.Co1} (hT : NRep T t)
    (hW : NRep W w) (h : Native.mul T W = Native.mul W T) :
    t ∈ centralizer ({w} : Set NativeSporadic.Co1) :=
  mem_centralizer_singleton_iff.2 (NRep.unique (hT.mul hW) (by rw [h]; exact hW.mul hT))

theorem mem_qOf_of_rows {p : Native.Rows × Native.Rows} {x : NativeSporadic.Co1} (hp : CRep p x)
    {Y : Native.Rows} {y : Vt} (hY : NRep Y y)
    (hYv : CFSG.Sporadic.Co1.InvNative.validRows Y = true)
    (h : qPts.contains (Native.mul (Native.mul p.2 Y) p.1) = true) :
    (y : NativeSporadic.Co1) ∈ qOf ((x • vA : Vt) : NativeSporadic.Co1) := by
  rw [coe_smul_conjVert, mem_qOf_conj]
  show _ ∈ qOf aNC
  rw [qOf_aNC]
  exact (mem_twoAQNC_iff_contains ((hp.2.1.mul hY).mul hp.1)
    (validRows_mul (validRows_mul hp.2.2.2 hYv) hp.2.2.1)).2 h

theorem locTri_spec (j : Fin 3) :
    (tauT j • vA = vE ∧ tauT j • vE = vA ∧ tauT j • uT j = uT j ∧
      tauT j ∈ centralizer ({(wT j : NativeSporadic.Co1)} : Set NativeSporadic.Co1)) ∧
    (rhoT j • vA = vE ∧ rhoT j • vE = uT j ∧ rhoT j • uT j = vA ∧
      rhoT j ∈ centralizer ({(wT j : NativeSporadic.Co1)} : Set NativeSporadic.Co1)) ∧
    ∀ x ∈ ({vA, vE, uT j} : Set Vt),
      (x : NativeSporadic.Co1) ∈ qOf (wT j : NativeSporadic.Co1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hloc⟩ := triCheck_parts
  have h := hloc j j.2
  unfold locTriOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hw⟩, ht1⟩, ht2⟩, hr1⟩, hr2⟩, htA⟩, htE⟩, htU⟩, htW⟩, hrA⟩, hrE⟩,
    hrU⟩, hrW⟩, hqA⟩, hqE⟩, hqU⟩ := h
  have hT := nrep_gEl (dagOK_parts dagOK_true).1 (tauIdx.getD j 0)
  have hTi := nrep_gElInv dagOK_true ht1 ht2
  have hR := nrep_gEl (dagOK_parts dagOK_true).1 (rhoIdx.getD j 0)
  have hRi := nrep_gElInv dagOK_true hr1 hr2
  have hp := crep_wP hw
  have hW := nrep_vtxR hp.1 hp.2.1
  have hA := nrep_aNC
  have hE1 := nrep_repV (show 1 < 10 by norm_num)
  have hU := nrep_cV hk
  have hEv := valid_repRows (show 1 < 10 by norm_num)
  refine ⟨⟨smul_eq_of_rows hT hTi hA hE1 htA, smul_eq_of_rows hT hTi hE1 hA htE,
    smul_eq_of_rows hT hTi hU hU htU, mem_centralizer_of_rows hT hW htW⟩,
    ⟨smul_eq_of_rows hR hRi hA hE1 hrA, smul_eq_of_rows hR hRi hE1 hU hrE,
    smul_eq_of_rows hR hRi hU hA hrU, mem_centralizer_of_rows hR hW hrW⟩, ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact mem_qOf_of_rows hp hA twoA_misc_parts.2.2.2.2.2.1 hqA
  · exact mem_qOf_of_rows hp hE1 hEv hqE
  · exact mem_qOf_of_rows hp hU (valid_pts hk) hqU

@[expose] noncomputable def triGrp (j : Fin 3) : Subgroup NativeSporadic.Co1 :=
  MulAction.stabilizer NativeSporadic.Co1 ({vA, vE, uT j} : Set Vt) ⊓
    centralizer ({(wT j : NativeSporadic.Co1)} : Set NativeSporadic.Co1)

theorem image_eq_of_mem_triGrp {j : Fin 3} {g : NativeSporadic.Co1} (hg : g ∈ triGrp j) :
    (g • ·) '' ({vA, vE, uT j} : Set Vt) = {vA, vE, uT j} := by
  rw [Set.image_smul]
  exact MulAction.mem_stabilizer_iff.1 (mem_inf.1 hg).1

theorem tauT_mem (j : Fin 3) : tauT j ∈ triGrp j := by
  obtain ⟨⟨ha, he, hu, hw⟩, -⟩ := locTri_spec j
  refine mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 ?_, hw⟩
  rw [← Set.image_smul, image_smul_triple, ha, he, hu, Set.insert_comm]

theorem rhoT_mem (j : Fin 3) : rhoT j ∈ triGrp j := by
  obtain ⟨-, ⟨ha, he, hu, hw⟩, -⟩ := locTri_spec j
  refine mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 ?_, hw⟩
  rw [← Set.image_smul, image_smul_triple, ha, he, hu]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun h => h.elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim (fun h => Or.inr (Or.inr h)) Or.inl),
    fun h => h.elim (fun h => Or.inr (Or.inr h))
      (fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))⟩

@[expose] noncomputable def titsDataNative :
    TitsDataBy (a2Graph aNC) triT NativeSporadic.Co1 (Fin 3) :=
  TitsDataBy.ofOrbits vA vE uT (centralizer ({aNC} : Set NativeSporadic.Co1)) (edgeStab vA vE)
    triGrp (fun g _ _ h => a2Graph_adj_smul g h) a2_preconnected a2_triangulableBy
    a2_adj_vA_vE
    (fun y hy => by
      obtain ⟨k, hk, rfl⟩ := (a2_adj_vA_iff y).1 hy
      exact ⟨k, (smul_vA_eq_iff k).2 hk, rfl⟩)
    ⟨gElt swapIdx, swap_smul⟩ (fun g => (smul_vA_eq_iff g).symm) (fun _ => mem_edgeStab)
    (fun _ _ hg => image_eq_of_mem_triGrp hg)
    (fun j => ⟨tauT j, tauT_mem j, (locTri_spec j).1.1, (locTri_spec j).1.2.1⟩)
    (fun j => ⟨rhoT j, rhoT_mem j, (locTri_spec j).2.1.1, (locTri_spec j).2.1.2.1,
      (locTri_spec j).2.1.2.2.1⟩)

end CFSG.Sporadic.Co1Patterson
