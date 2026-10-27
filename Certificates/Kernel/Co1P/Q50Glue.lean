module

public import Certificates.Kernel.Co1P.Defs21150Q
public import Certificates.Kernel.Co1P.Q2Glue
public import CFSG.Certificates.Kernel.Co1PPathMSound
public import Certificates.Kernel.Co1P.Defs21150
public import Certificates.Kernel.Co1P.Defs21150S

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native CertificateChecks.KernelCo1B

theorem chunks_all' {F : Nat → Nat → Bool} {N nc : Nat} (hN : N ≤ 64 * nc)
    (h : ∀ c < nc, chunkK N (F c) c = true) : ∀ i < N, F (i / 64) i = true := by
  intro i hi
  have hc : i / 64 < nc := by omega
  have h1 := allN_true (h _ hc) (i % 64) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul 64 (i / 64)) (i % 64) = i := Nat.div_add_mod i 64
  have h2 : orB (Nat.ble N i) (F (i / 64) i) = true := by
    rw [e] at h1
    exact h1
  rcases orB_true h2 with h3 | h3
  · exact absurd (Nat.le_of_ble_eq_true h3) (by omega)
  · exact h3

theorem bk_parts (h : andB (Nat.beq (lenL BK) 8) (invsOK BK BIK) = true) : invsOK BK BIK = true :=
  (CFSG.KC.TreeK.andB_true h).2

theorem orbClosed_of {o : Orb} {N : Nat} (hs : o.c.pts.size = N) (P : Nat → Nat)
    (hp : ∀ i < N, o.c.pts[i]! = unpackR 24 (P i))
    (hc : ∀ i < N, ∀ l < 8, (ptSet o).contains (unpackR 24 (brI l (P i))) = true) :
    orbClosed brayArr brayInvArr o = true := by
  unfold orbClosed
  simp only [List.all_eq_true, List.mem_range]
  intro i hi l hl
  rw [brayArr_size] at hl
  rw [hs] at hi
  rw [hp i hi, brayArr_get hl, brayInvArr_get hl, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
  exact hc i hi l hl

theorem closQ_parts (h : closQ = true) : orbChk BK BIK 8 (repK 0) 9 (recsT orbQMasks) = true ∧
    sincK (sortP 9 (modL ptsQ)) = true ∧ treeAll 9 (sortP 9 (modL ptsQ)) = true ∧
    (ptsQ.all fun P => allN 8 fun l => memKT (keyK (brI l P)) (treeOf 9 (sortP 9 (modL ptsQ)))) = true := by
  unfold closQ at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  obtain ⟨h3, h4⟩ := CFSG.KC.TreeK.andB_true h2
  obtain ⟨h5, h6⟩ := CFSG.KC.TreeK.andB_true h3
  exact ⟨h1, h5, h6, h4⟩

theorem exact_Q (h : closQ = true) (hb : andB (Nat.beq (lenL BK) 8) (invsOK BK BIK) = true) :
    exactOK orbQ zRows 270 = true := by
  obtain ⟨hc, hs, ha, himg⟩ := closQ_parts h
  have hw := orbChk_walks hc
  have hG := fun l (hl : l < 8) => brayArr_get hl
  have hGi := fun l (hl : l < 8) => brayInvArr_get hl
  have hsz : orbQ.c.pts.size = 270 := orbQ_size'
  have hlen : ptsQ.length = 270 := by
    rw [ptsQ, ptsL_length hw.1 hw.2, recsQ_len]
  unfold exactOK
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, hsz⟩
  · rw [zRows, repRows_eq, orbQ_eq, treeT_eq]
    exact orbOK_of_chk brayArr_size hG hGi hc
  · refine orbClosed_of hsz (fun i => ptsQ[i]?.getD 0) (fun i hi => ?_) (fun i hi l hl => ?_)
    · rw [orbQ_eq, treeT_eq]
      exact mkOrbT_get hG hGi hw.1 hw.2 (by rw [recsQ_len]; exact hi)
    · rw [orbQ_eq, treeT_eq, ptSet, Std.HashSet.contains_ofList, mkOrbT_toList hG hGi hw.1 hw.2]
      change (ptsQ.map (unpackR 24)).contains _ = true
      rw [contains_map_memKT hs ha]
      have hm := List.all_eq_true.1 himg _ (List.getElem_mem (by rw [hlen]; exact hi))
      rw [List.getElem?_eq_getElem (by rw [hlen]; exact hi), Option.getD_some]
      exact allN_true hm l hl

theorem exact_E (hb : andB (Nat.beq (lenL BK) 8) (invsOK BK BIK) = true)
    (hcl : ∀ c < 197, closEC c = true) : exactOK orbE eRows 12600 = true := by
  have hw := brayTree_parts treeE_ok
  have hG := fun l (hl : l < 8) => brayArr_get hl
  have hGi := fun l (hl : l < 8) => brayInvArr_get hl
  have hcl' : ∀ c < 197, chunkK 12600 (closE (getL 0 JE c)) c = true := by
    intro c hc
    have h := hcl c hc
    unfold closEC at h
    rw [strictB_eq'] at h
    exact h
  have hall := chunks_all' (F := fun c => closE (getL 0 JE c)) (N := 12600) (nc := 197) (by decide) hcl'
  unfold exactOK
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, orbE_size'⟩
  · rw [CFSG.Sporadic.Co1Patterson.Native.eRows, repRows_eq, orbE_eq, treeT_eq]
    have hl := ptsL_length (GK := BK) (GiK := BIK) (R := repK 1) hw.1 hw.2
    rw [recsE_len] at hl
    refine orbOK_of_nodup brayArr_size hG hGi hw.1 hw.2 BK_len (bk_parts hb)
      (nodup_modL_of_keys (by decide) keyE_all hl fun i hi => ?_)
    have l1 := walk_length hw.1
    have l2 := walk_length hw.2
    rw [(conjL_get (repK 1) _ _ (l1.trans l2.symm)).2 i (by rw [l1, recsE_len]; exact hi), ptPE_eq hi]
    rfl
  · refine orbClosed_of orbE_size' ptPE (fun i hi => orbE_pt' hi) (fun k hk l hl => ?_)
    have h := hall k hk
    unfold closE at h
    rw [strictB_eq'] at h
    have h1 := allN_true h l hl
    rw [strictB_eq'] at h1
    obtain ⟨h2, h3⟩ := CFSG.KC.TreeK.andB_true h1
    rw [orbE_mem, memE_iff]
    exact ⟨_, lt_of_blt' h2, h3⟩

theorem orbOK_4c (hb : andB (Nat.beq (lenL BK) 8) (invsOK BK BIK) = true) :
    orbOK brayArr brayInvArr (repRows 3) orb4c = true := by
  have hN : (recsT orb4cMasks).length + 1 = 34560 := by rw [recs4C_len]
  rw [orb4c, repRows_eq, treeT_eq]
  exact orbOK_of_nodup brayArr_size (fun l hl => brayArr_get hl) (fun l hl => brayInvArr_get hl)
    walk4C_hs walk4C_his BK_len (bk_parts hb)
    (ptsL_nodup walk4C_hs walk4C_his recs4C_pin hN keys4C (by decide))

theorem pt4M_eq (hr : recsEqK r4W (recsT orb4cMasks) 0 = true) (ht : allN 43 th4_chunk = true)
    {i : Nat} (hi : i < 34560) (h : (pt4M i).2 = true) :
    (pt4M i).1 = (ptsL BK BIK 8 (repK 3) (recsT orb4cMasks))[i]?.getD 0 := by
  have hp : ∀ i < 2692, pinAt (hsAct BK) oneK th4 r4W i = true :=
    chunks_all (f := pinAt (hsAct BK) oneK th4 r4W) (N := 2692) (nc := 43) (by decide)
      fun c hc => (CFSG.KC.TreeK.andB_true (allN_true ht c hc)).1
  have hpi : ∀ i < 2692, pinAt (hisAct BIK) oneK thi4 r4W i = true :=
    chunks_all (f := pinAt (hisAct BIK) oneK thi4 r4W) (N := 2692) (nc := 43) (by decide)
      fun c hc => (CFSG.KC.TreeK.andB_true (allN_true ht c hc)).2
  have l1 := walk_length walk4C_hs
  have l2 := walk_length walk4C_his
  have hi' : i < (recsT orb4cMasks).length + 1 := by rw [recs4C_len]; exact hi
  rw [pt4M, ptM_sound (by rw [recs4C_len]; decide) walk4C_hs walk4C_his hr hp hpi hi' h, ptsL,
    (conjL_get (repK 3) _ _ (l1.trans l2.symm)).2 i (by rw [l1]; exact hi')]
  rfl

theorem exact_4c (hb : andB (Nat.beq (lenL BK) 8) (invsOK BK BIK) = true)
    (hr : recsEqK r4W (recsT orb4cMasks) 0 = true) (ht : allN 43 th4_chunk = true)
    (hcl : ∀ c < 540, clos4C c = true) : exactOK orb4c (repRows 3) 34560 = true := by
  have hG := fun l (hl : l < 8) => brayArr_get hl
  have hGi := fun l (hl : l < 8) => brayInvArr_get hl
  have hlen4 : (ptsL BK BIK 8 (repK 3) (recsT orb4cMasks)).length = 34560 := by
    rw [ptsL_length walk4C_hs walk4C_his, recs4C_len]
  have hcl' : ∀ c < 540, chunkK 34560 (clos4 (getL 0 J4 c)) c = true := by
    intro c hc
    have h := hcl c hc
    unfold clos4C at h
    rw [strictB_eq'] at h
    exact h
  have hall := chunks_all' (F := fun c => clos4 (getL 0 J4 c)) (N := 34560) (nc := 540) (by decide) hcl'
  unfold exactOK
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨orbOK_4c hb, ?_⟩, orb4c_size⟩
  refine orbClosed_of orb4c_size (fun i => (ptsL BK BIK 8 (repK 3) (recsT orb4cMasks))[i]?.getD 0)
    (fun i hi => ?_) (fun i hi l hl => ?_)
  · rw [orb4c, repRows_eq, treeT_eq]
    exact mkOrbT_get hG hGi walk4C_hs walk4C_his (by rw [recs4C_len]; exact hi)
  · have h := hall i hi
    unfold clos4 at h
    obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
    rw [strictB_eq'] at h2
    have h3 := allN_true h2 l hl
    rw [strictB_eq'] at h3
    obtain ⟨h4, h5⟩ := CFSG.KC.TreeK.andB_true h3
    obtain ⟨h6, h7⟩ := CFSG.KC.TreeK.andB_true h5
    have hj := lt_of_blt' h4
    rw [pt4M_eq hr ht hj h6, pt4M_eq hr ht hi h1] at h7
    rw [orb4c, repRows_eq, treeT_eq, contains_mkOrbT hG hGi walk4C_hs walk4C_his, List.any_eq_true]
    refine ⟨_, List.getElem_mem (by rw [hlen4]; exact hj), ?_⟩
    have hj' := hlen4.symm ▸ hj
    rw [List.getElem?_eq_getElem hj', Option.getD_some] at h7
    exact h7

theorem pfK_eq (w : Nat) (C : List Nat) (c s : Nat) : pfK w C c (getL 0 C c) s = tabK w C s := by
  unfold pfK
  by_cases hs : s / 64 = c
  · have e : Nat.beq (Nat.div s 64) c = true := by rw [Nat.beq_eq]; exact hs
    rw [e]
    change fget (getL 0 C c) (s % 64) w = fget (getL 0 C (s / 64)) (s % 64) w
    rw [hs]
  · have e : Nat.beq (Nat.div s 64) c = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hs
    rw [e]

theorem orbOK_A4 (hb : andB (Nat.beq (lenL BK) 8) (invsOK BK BIK) = true)
    (hh : (treePts (hsAct BK) 8 oneK (recsT orbA4Masks)).2 = true)
    (hhi : (treePts (hisAct BIK) 8 oneK (recsT orbA4Masks)).2 = true)
    (hr : recsEqK rA4 (recsT orbA4Masks) 0 = true) (hlen : Nat.beq (recsT orbA4Masks).length 60479 = true)
    (hk : ∀ c < 945, keyA4_chunk c = true) :
    orbOK brayArr brayInvArr (repRows 2) orbA4 = true ∧ orbA4.c.pts.size = 60480 := by
  have hl : (recsT orbA4Masks).length = 60479 := by
    rw [Nat.beq_eq] at hlen
    exact hlen
  have hN : (recsT orbA4Masks).length + 1 = 60480 := by rw [hl]
  have hk' : ∀ c < 945, chunkK 60480 (keyAtP 60480 64 skA4 ixA4 ptA4) c = true := by
    intro c hc
    have h := hk c hc
    unfold keyA4_chunk at h
    rw [strictB_eq', strictB_eq'] at h
    have e1 : pfK 64 SKA4 c (getL 0 SKA4 c) = skA4 := funext fun s => pfK_eq 64 SKA4 c s
    have e2 : pfK 16 IXA4 c (getL 0 IXA4 c) = ixA4 := funext fun s => pfK_eq 16 IXA4 c s
    rw [e1, e2] at h
    exact h
  have keys := chunks_all (f := keyAtP 60480 64 skA4 ixA4 ptA4) (N := 60480) (nc := 945) (by decide) hk'
  refine ⟨?_, ?_⟩
  · rw [orbA4, repRows_eq, treeT_eq]
    exact orbOK_of_nodup brayArr_size (fun l hl => brayArr_get hl) (fun l hl => brayInvArr_get hl)
      hh hhi BK_len (bk_parts hb) (ptsL_nodup hh hhi hr hN keys (by decide))
  · rw [orbA4, repRows_eq, treeT_eq, mkOrbT_size, hl]

theorem dagOK_of (h : dagInvK = true) : CFSG.Sporadic.Co1Patterson.Native.dagOK = true := by
  unfold CFSG.Sporadic.Co1Patterson.Native.dagOK
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨by rw [gDag_eq], by rw [gDag_eq, List.length_map, GDS_len]; rfl⟩, fun j hj => ?_⟩
  have hj' := List.mem_range.1 hj
  rw [gEl_eq, gElInv_eq, Nat.add_sub_cancel, Bool.and_eq_true, Bool.and_eq_true,
    CFSG.KC.F2W.mul_unpackW, CFSG.KC.Co1B.one_eq, beq_unpack]
  exact ⟨⟨validRows_unpackR _, validRows_unpackR _⟩, allN_true h j hj'⟩

theorem forceKT_eq {α : Sort _} : ∀ (t : KT) (k : KT → α), forceKT t k = k t
  | .leaf, _ => rfl
  | .node l x r, k => by
    change forceKT l (fun l' => Nat.rec (motive := fun _ => α) (forceKT r fun r' => k (KT.node l' 0 r'))
      (fun n _ => forceKT r fun r' => k (KT.node l' (Nat.succ n) r')) x) = _
    rw [forceKT_eq l]
    cases x with
    | zero => exact forceKT_eq r _
    | succ n => exact forceKT_eq r _

theorem qTreeOK_of (hq : andB qClosT (distinctK 10 (modL QL)) = true) : qTreeOK = true := by
  obtain ⟨hc0, hd⟩ := CFSG.KC.TreeK.andB_true hq
  unfold qClosT at hc0
  rw [strictL_eq] at hc0
  unfold qClosS at hc0
  obtain ⟨hsa, hc⟩ := CFSG.KC.TreeK.andB_true hc0
  obtain ⟨hsq, hta⟩ := CFSG.KC.TreeK.andB_true hsa
  rw [forceKT_eq] at hc
  have hT : CFSG.Sporadic.Co1Block.twoAQTree = CFSG.Sporadic.Co1Block.gtOfMasks
      CFSG.Sporadic.Co1Block.twoAQRows.toArray (treeArr (recsT CFSG.Sporadic.Co1Block.twoAQMasks)) := by
    rw [CFSG.Sporadic.Co1Block.twoAQTree, treeOfMasks_eq]
    rfl
  obtain ⟨hs, hg⟩ := gtOfMasks_get (fun l hl => twoAQ_get hl) treeAQ_ok
  have hl := walk_length treeAQ_ok
  have hG8 : CFSG.Sporadic.Co1Block.twoAQRows.toArray.size = 8 := rfl
  have hpts : (CFSG.Sporadic.Co1Block.gtOfMasks CFSG.Sporadic.Co1Block.twoAQRows.toArray
      (treeArr (recsT CFSG.Sporadic.Co1Block.twoAQMasks))).pts.toList = QL.map (unpackR 24) :=
    toList_eq_map (L := QL) (by rw [hs]; exact hl.symm) fun j hj => by
      rw [hg j (by rw [← hl]; exact hj)]
      rfl
  unfold qTreeOK CFSG.Sporadic.Co1.TwoBNative.gtOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, CFSG.Sporadic.Th.allIn_eq_true]
  rw [hT]
  have ep : (CFSG.Sporadic.Co1Block.gtOfMasks CFSG.Sporadic.Co1Block.twoAQRows.toArray
      (treeArr (recsT CFSG.Sporadic.Co1Block.twoAQMasks))).par =
        (treeArr (recsT CFSG.Sporadic.Co1Block.twoAQMasks)).1 := rfl
  have el : (CFSG.Sporadic.Co1Block.gtOfMasks CFSG.Sporadic.Co1Block.twoAQRows.toArray
      (treeArr (recsT CFSG.Sporadic.Co1Block.twoAQMasks))).lab =
        (treeArr (recsT CFSG.Sporadic.Co1Block.twoAQMasks)).2 := rfl
  have em : ∀ a b : Nat, CFSG.Sporadic.SmallF2.Native.mulRows 24 (unpackR 24 a) (unpackR 24 b) =
      unpackR 24 (mulWK a b) := fun a b => CFSG.KC.F2W.mul_unpackW a b
  rw [ep, el]
  refine ⟨⟨⟨⟨⟨by rw [hs]; omega, by rw [hs, treeArr_size]⟩, by rw [hs]; simp [treeArr]⟩, ?_⟩, ?_⟩, ?_⟩
  · intro i _ hi
    rw [hs] at hi
    unfold CFSG.Sporadic.Co1.TwoBNative.gtPointOK
    rw [ep, el, Bool.and_eq_true]
    refine ⟨by rw [hg i hi]; exact validRows_unpackR _, ?_⟩
    rcases i with _ | j
    · simp only [beq_self_eq_true, ↓reduceIte, beq_iff_eq]
      rw [hg 0 hi, walkAt_zero treeAQ_ok]
      exact CFSG.KC.Co1B.one_eq.symm
    · have hj : j < (recsT CFSG.Sporadic.Co1Block.twoAQMasks).length := by omega
      obtain ⟨hp, hlb, he⟩ := walkAt_succ treeAQ_ok hj
      simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
      rw [treeArr_par hj, treeArr_lab hj, hG8]
      refine ⟨⟨by omega, hlb⟩, ?_⟩
      rw [hg (j + 1) hi, hg _ (by omega), twoAQ_get hlb, he, em]
      rfl
  · rw [hpts]
    exact distinctKeys_of_nodup (nodup_keys (distinctK_sound hd))
  · unfold CFSG.Sporadic.Co1.TwoBNative.gtClosed
    simp only [CFSG.Sporadic.Th.allIn_eq_true]
    intro i _ hi l _ hl'
    rw [hs] at hi
    rw [hG8] at hl'
    rw [Std.HashSet.contains_ofList, hpts, hg i hi, twoAQ_get hl', em, contains_map_memKT hsq hta]
    have hQ : (treePts (hisAct QG) 8 oneK (recsT CFSG.Sporadic.Co1Block.twoAQMasks)).1 = QL := rfl
    have hi' : i < QL.length := by rw [← hQ, hl]; exact hi
    have h1 := List.all_eq_true.1 hc _ (List.getElem_mem hi')
    have h2 := allN_true h1 l hl'
    rw [walkAt, hQ, List.getElem?_eq_getElem hi', Option.getD_some]
    exact h2

theorem rep11_eq (i : Nat) : rep11 i = unpackR 24 (rep11K i) := by
  unfold rep11 rep11K
  by_cases h0 : i = 0
  · subst h0
    rw [iotaA_K, if_pos rfl]
    rfl
  · have hb : (i == 0) = false := by simpa using h0
    rw [hb, ite_eq_right h0, repRows_eq]
    rfl

theorem invCheck_of (h : invChkK = true) : invCheck = true := by
  unfold invCheck
  unfold invChkK at h
  rw [List.all_eq_true] at h ⊢
  intro i hi
  have h1 := h i hi
  rw [rep11_eq]
  unfold invK at h1
  unfold invOK
  dsimp only
  rw [iotaA_K, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, qPts_contains, qPts_contains]
  obtain ⟨h2, h3⟩ := CFSG.KC.TreeK.andB_true h1
  obtain ⟨h4, h5⟩ := CFSG.KC.TreeK.andB_true h2
  obtain ⟨h6, h7⟩ := CFSG.KC.TreeK.andB_true h3
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨validRows_unpackR _, validRows_unpackR _⟩, CFSG.KC.Co1F2.orderIs_sound h4⟩, h5⟩, h6⟩, h7⟩

end CertificateChecks.KernelCo1P

end
