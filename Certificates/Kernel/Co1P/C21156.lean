module

public import Certificates.Kernel.Co1P.C21158
public import Certificates.Kernel.Co1P.Chk21156
public import Certificates.Kernel.Co1P.Chk21156L
public import Certificates.Kernel.Co1P.PinEGlue
public import CFSG.Certificates.Kernel.Co1POrbSound

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native CertificateChecks.KernelCo1B

theorem eqLK_sound : ∀ (xs ys : List Nat), eqLK xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: xs, y :: ys, h => by
    obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
    rw [Nat.eq_of_beq_eq_true h1, eqLK_sound xs ys h2]

theorem gensArr_Ke {l : Nat} (hl : l < 6) : (gensArr gensKe)[l]! = unpackR 24 (getL 0 GE l) := by
  have e : getL 0 GE l = getL oneK GDS (gensKe.getD l 0 - 1) := by interval_cases l <;> rfl
  have hl' : l < gensKe.length := hl
  rw [e, gensArr, getElem!_pos _ l (by simpa using hl'),
    List.getElem_toArray, List.getElem_map, gEl_eq, ← List.getD_eq_getElem _ 0]

theorem gensInvArr_Ke {l : Nat} (hl : l < 6) :
    (gensInvArr gensKe)[l]! = unpackR 24 (getL 0 GEI l) := by
  have e : getL 0 GEI l = getL oneK GDIS (gensKe.getD l 0 - 1) := by interval_cases l <;> rfl
  have hl' : l < gensKe.length := hl
  rw [e, gensInvArr, getElem!_pos _ l (by simpa using hl'),
    List.getElem_toArray, List.getElem_map, gElInv_eq, ← List.getD_eq_getElem _ 0]

theorem gensArr_Ke_size : (gensArr gensKe).size = 6 := by simp [gensArr, gensKe]

theorem gensArr_KeL : gensArr gensKe = (GE.map (unpackR 24)).toArray := by
  unfold gensArr GE
  rw [List.map_map, List.map_congr_left (fun j _ => gEl_eq j)]
  rfl

theorem orbE_pt {k : Nat} (hk : k < 12600) : orbE.c.pts[k]! = unpackR 24 (ptE k) := by
  rw [orbE_pt' hk, ptPE_eq hk]

theorem loc_tree (k : Nat) (ms : List Nat) (hk : k < 12600) :
    mkOrbT (gensArr gensKe) (gensInvArr gensKe) orbE.c.pts[k]! (treeT ms) =
      mkOrbT (gensArr gensKe) (gensInvArr gensKe) (unpackR 24 (ptE k)) (treeArr (recsT ms)) := by
  rw [orbE_pt hk, treeT_eq]

theorem locOrbs_eq : locOrbs orbE =
    [mkOrbT (gensArr gensKe) (gensInvArr gensKe) (unpackR 24 (ptE 202)) (treeArr (recsT loc202Masks)),
      mkOrbT (gensArr gensKe) (gensInvArr gensKe) (unpackR 24 (ptE 2348)) (treeArr (recsT loc2348Masks)),
      mkOrbT (gensArr gensKe) (gensInvArr gensKe) (unpackR 24 (ptE 3940))
        (treeArr (recsT loc3940Masks))] := by
  have hr : triRoots = [202, 2348, 3940] := rfl
  rw [locOrbs, hr]
  simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil]
  rw [loc_tree _ _ (by decide), loc_tree _ _ (by decide), loc_tree _ _ (by decide)]

theorem t192_eq : t192Orb orbE =
    mkOrbT (gensArr gensKe) (gensInvArr gensKe) (unpackR 24 (ptE 35)) (treeArr (recsT t192Masks)) := by
  have hr : t192Root = 35 := rfl
  rw [t192Orb, hr, loc_tree _ _ (by decide)]

theorem locOK_mk {k : Nat} {ms : List Nat} (h : orbChk GE GEI 6 (ptE k) 8 (recsT ms) = true) :
    orbOK (gensArr gensKe) (gensInvArr gensKe) (unpackR 24 (ptE k))
      (mkOrbT (gensArr gensKe) (gensInvArr gensKe) (unpackR 24 (ptE k)) (treeArr (recsT ms))) = true :=
  orbOK_of_chk gensArr_Ke_size (fun _ hl => gensArr_Ke hl) (fun _ hl => gensInvArr_Ke hl) h

theorem loc_toList {k : Nat} {ms : List Nat} (h : orbChk GE GEI 6 (ptE k) 8 (recsT ms) = true) :
    (mkOrbT (gensArr gensKe) (gensInvArr gensKe) (unpackR 24 (ptE k)) (treeArr (recsT ms))).c.pts.toList =
      (ptsGE (ptE k) ms).map (unpackR 24) :=
  mkOrbT_toList (fun _ hl => gensArr_Ke hl) (fun _ hl => gensInvArr_Ke hl) (orbChk_walks h).1
    (orbChk_walks h).2

theorem lset_eq : ((locOrbs orbE).flatMap fun f => f.c.pts.toList) = LP.map (unpackR 24) := by
  rw [locOrbs_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [loc_toList loc_ok.1, loc_toList loc_ok.2.1, loc_toList loc_ok.2.2, LP, List.map_append,
    List.map_append, List.append_assoc]

theorem t192_toList : (t192Orb orbE).c.pts.toList = TP.map (unpackR 24) := by
  rw [t192_eq, loc_toList t192_ok]
  rfl

theorem pins_parts : (sincK SLP = true ∧ treeAll 9 SLP = true) ∧ (sincK STP = true ∧ treeAll 8 STP = true) ∧
    SLP = sortP 9 (modL LP) ∧ STP = sortP 8 (modL TP) := by
  have h := pins_ok
  unfold pinsOK sortedOK at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  obtain ⟨h3, h4⟩ := CFSG.KC.TreeK.andB_true h1
  obtain ⟨h5, h6⟩ := CFSG.KC.TreeK.andB_true h2
  exact ⟨CFSG.KC.TreeK.andB_true h3, CFSG.KC.TreeK.andB_true h4, eqLK_sound _ _ h5,
    eqLK_sound _ _ h6⟩

theorem lset_mem (X : Nat) : (Std.HashSet.ofList ((locOrbs orbE).flatMap fun f => f.c.pts.toList)).contains
    (unpackR 24 X) = memKT (keyK X) (treeOf 9 SLP) := by
  obtain ⟨⟨h1, h2⟩, -, e, -⟩ := pins_parts
  rw [e] at h1 h2
  rw [Std.HashSet.contains_ofList, lset_eq, contains_map_memKT h1 h2, e]
  rfl

theorem tset_mem (X : Nat) : (ptSet (t192Orb orbE)).contains (unpackR 24 X) =
    memKT (keyK X) (treeOf 8 STP) := by
  obtain ⟨-, ⟨h1, h2⟩, -, e⟩ := pins_parts
  rw [e] at h1 h2
  rw [ptSet, Std.HashSet.contains_ofList, t192_toList, contains_map_memKT h1 h2, e]
  rfl

theorem tri_all : ∀ k < 12600, triAtW (treeOf 9 SLP) (treeOf 8 STP) k = true :=
  chunks_all (f := triAtW (treeOf 9 SLP) (treeOf 8 STP)) (N := 12600) (nc := 197) (by decide)
    fun c hc => TriE.all c hc

theorem orbQ_hs' {i : Nat} (hi : i < 270) : orbQ.hs[i]! = unpackR 24 (hsW orbQMasks i) := by
  have hj : i < (recsT orbQMasks).length + 1 := by rw [recsQ_len]; omega
  rw [orbQ_eq]
  exact bray_hs treeQ_ok _ hj

theorem orbQ_his' {i : Nat} (hi : i < 270) : orbQ.his[i]! = unpackR 24 (hisW orbQMasks i) := by
  have hj : i < (recsT orbQMasks).length + 1 := by rw [recsQ_len]; omega
  rw [orbQ_eq]
  exact bray_his treeQ_ok _ hj

theorem orbQ_size' : orbQ.c.pts.size = 270 := by
  rw [orbQ_eq, treeT_eq, mkOrbT_size, recsQ_len]

theorem locTri_of {j k ti ri w : Nat} (hk : triRoots.getD j 0 = k) (hk' : k < 12600)
    (ht : tauIdx.getD j 0 = ti) (hr : rhoIdx.getD j 0 = ri) (hw : triW.getD j 0 = w) (hw' : w < 270)
    (h1 : 1 ≤ ti) (h2 : ti ≤ 190) (h3 : 1 ≤ ri) (h4 : ri ≤ 190)
    (h : locK (ptPE k) (getL oneK GDS (ti - 1)) (getL oneK GDIS (ti - 1)) (getL oneK GDS (ri - 1))
      (getL oneK GDIS (ri - 1)) w = true) : locTriOK orbE j = true := by
  unfold locK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, q1, q2, q3⟩ := h
  unfold locTriOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
  rw [hk, ht, hr, hw, orbE_size', orbQ_size', wP, vtxR, conjA, orbE_pt' hk', orbQ_hs' hw',
    orbQ_his' hw', gEl_eq, gElInv_eq, gEl_eq, gElInv_eq, iotaA_K, repRows_eq, repX_eq, repXi_eq]
  simp only [CFSG.KC.F2W.mul_unpackW, qPts_contains]
  exact ⟨hk', hw', h1, h2, h3, h4, unpack_eq e1, unpack_eq e2, unpack_eq e3, unpack_eq e4,
    unpack_eq e5, unpack_eq e6, unpack_eq e7, unpack_eq e8, q1, q2, q3⟩

theorem tri : triCheck = true := by
  have hsm := tri_small
  unfold triSmallK at hsm
  simp only [andB_eq, Bool.and_eq_true] at hsm
  obtain ⟨⟨s1, s2⟩, s3, s4, l1, l2, l3⟩ := hsm
  have hc := tri_cone
  unfold triConeK at hc
  simp only [andB_eq, Bool.and_eq_true] at hc
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc
  have hci : coneIdx = 202 := rfl
  have hck : coneK2 = 9987 := rfl
  have htr : t192Root = 35 := rfl
  have hsw : swapIdx = 176 := rfl
  unfold triCheck
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
  rw [hci, hck, htr, hsw]
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gEl_eq, gElInv_eq, iotaA_K, repRows_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
    exact unpack_eq s1
  · rw [gEl_eq, gElInv_eq, iotaA_K, repRows_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
    exact unpack_eq s2
  · unfold centOK
    rw [gensArr_KeL, List.all_toArray, List.all_map, List.all_eq_true]
    intro g hg
    have hg' := List.all_eq_true.1 s3 g hg
    rw [Function.comp_apply, iotaA_K, repRows_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW,
      CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, beq_unpack, beq_unpack]
    exact hg'
  · rw [locOrbs_eq]
    rfl
  · rw [locOrbs_eq, List.all_eq_true]
    intro j hj
    have hj' : j < 3 := List.mem_range.1 hj
    interval_cases j
    · rw [orbE_pt (by decide)]
      exact locOK_mk loc_ok.1
    · rw [orbE_pt (by decide)]
      exact locOK_mk loc_ok.2.1
    · rw [orbE_pt (by decide)]
      exact locOK_mk loc_ok.2.2
  · rw [t192_eq, orbE_pt (by decide)]
    exact locOK_mk t192_ok
  · rw [orbE_size', List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    have h := tri_all k hk'
    unfold triAtW at h
    unfold adjC
    rw [orbE_pt' hk', repX_eq, repXi_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, orbE_mem,
      lset_mem, tset_mem]
    simp only [orB_eq, notB_eq] at h
    rw [Bool.or_assoc]
    exact h
  · rw [orbE_size']
    decide
  · rw [orbE_size']
    decide
  · rw [orbE_size']
    decide
  · unfold adjC
    rw [orbE_pt' (by decide), repX_eq, repXi_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW,
      orbE_mem]
    exact c1
  · unfold adjC xeK xeiK
    rw [orbE_pt' (by decide), orbE_hs' (by decide), orbE_his' (by decide), repX_eq, repXi_eq]
    simp only [CFSG.KC.F2W.mul_unpackW]
    rw [orbE_mem]
    exact c2
  · rw [orbE_pt' (by decide), lset_mem]
    exact c3
  · rw [orbE_pt' (by decide), orbE_hs' (by decide), orbE_his' (by decide)]
    simp only [CFSG.KC.F2W.mul_unpackW]
    rw [lset_mem]
    exact c4
  · rw [gEl_eq, gElInv_eq, orbE_pt' (by decide), orbE_pt' (by decide), CFSG.KC.F2W.mul_unpackW,
      CFSG.KC.F2W.mul_unpackW]
    exact unpack_eq s4
  · rw [orbE_pt' (by decide), orbE_hs' (by decide), orbE_his' (by decide), gEl_eq, gElInv_eq]
    simp only [CFSG.KC.F2W.mul_unpackW]
    rw [lset_mem]
    exact c5
  · rw [List.all_eq_true]
    intro j hj
    have hj' : j < 3 := List.mem_range.1 hj
    interval_cases j
    · exact locTri_of rfl (by decide) rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by decide) l1
    · exact locTri_of rfl (by decide) rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by decide) l2
    · exact locTri_of rfl (by decide) rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by decide) l3

open Certificates in
theorem c21156 : CFSG.Sporadic.Co1Patterson.Native.triCheck = true := tri

end CertificateChecks.KernelCo1P

end
