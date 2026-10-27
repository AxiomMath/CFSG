module

public import Certificates.Kernel.Co1P.Defs21154
public import Certificates.Kernel.Co1P.C21151
public import Certificates.Kernel.Co1P.C21153

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native CertificateChecks.KernelCo1B

@[expose] def UP (p : Nat × Nat) : Rows × Rows := (unpackR 24 p.1, unpackR 24 p.2)

theorem vtx_eq (p : Nat × Nat) : vtxR (UP p).1 (UP p).2 = unpackR 24 (vtxP p) := by
  rw [UP, vtxR, conjA, iotaA_K, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
  rfl

theorem nb_eq (p : Nat × Nat) {k : Nat} (hk : k < 12600) : nbrX orbE (UP p) k = UP (nbP p k) := by
  rw [nbrX, UP, UP, nbP, xeK_eq hk, xeiK_eq hk, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
  rfl

theorem adj_eq (p : Nat × Nat) (V : Nat) :
    adjC (ptSet orbE) (UP p).1 (UP p).2 (unpackR 24 V) = adjP p.1 p.2 V := adjC_eq' _ _ _

theorem pv_eq {vs : List (Nat × Nat)} (hl : vs.length = 5) (i : Nat) :
    pv (vs.map UP).toArray i = UP (pvK vs i) := by
  have hi : i % 5 < vs.length := by rw [hl]; exact Nat.mod_lt _ (by decide)
  unfold pv pvK
  rw [getElem!_pos _ _ (by simpa using hi), List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem _ _ hi]

theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]

theorem size_lt (k : Nat) : decide (k < orbE.c.pts.size) = Nat.blt k 12600 := by
  rw [orbE_size', blt_dec]

theorem blt_false {k : Nat} (hk : ¬ k < 12600) : Nat.blt k 12600 = false := by
  rw [blt_dec, decide_eq_false hk]

theorem list5 (a b c d e : Nat × Nat) :
    #[UP a, UP b, UP c, UP d, UP e] = ([a, b, c, d, e].map UP).toArray := rfl

theorem pc_eq : ∀ (P : PC) (vs : List (Nat × Nat)), vs.length = 5 →
    pcOK orbE (ptSet orbE) (vs.map UP).toArray P = pcK vs P
  | .chord r, vs, hl => by
    rw [pcOK, pcK, pv_eq hl, pv_eq hl, vtx_eq, vtx_eq, beq_unpack, adj_eq, orB_eq]
  | .centre r k, vs, hl => by
    rw [pcOK, pcK, size_lt]
    by_cases hk : k < 12600
    · rw [pv_eq hl, pv_eq hl, pv_eq hl, nb_eq _ hk, vtx_eq, vtx_eq, adj_eq, adj_eq]
      simp only [andB_eq, Bool.and_assoc]
    · rw [blt_false hk]
      simp [andB_eq]
  | .split r k P, vs, hl => by
    rw [pcOK, pcK, size_lt]
    by_cases hk : k < 12600
    · rw [pv_eq hl, pv_eq hl, pv_eq hl, pv_eq hl, nb_eq _ hk, vtx_eq, adj_eq, list5, pc_eq P _ rfl]
      simp only [andB_eq, Bool.and_assoc]
    · rw [blt_false hk]
      simp [andB_eq]

theorem one_pair : ((one, one) : Rows × Rows) = UP (oneK, oneK) := by
  rw [UP, ← CFSG.KC.Co1B.one_eq]

theorem xe_pair {c : Nat} (hc : c < 12600) : ((xeK orbE c, xeiK orbE c) : Rows × Rows) = UP (xeP c, xeiP c) := by
  rw [UP, xeK_eq hc, xeiK_eq hc]

theorem qc_eq : ∀ (C : QC) (b g : Nat × Nat), qcOK orbE (ptSet orbE) (UP b) (UP g) C = qcK b g C
  | .pent c c' P, b, g => by
    rw [qcOK, qcK, size_lt, size_lt]
    by_cases hc : c < 12600
    · by_cases hc' : c' < 12600
      · rw [xe_pair hc, xe_pair hc', one_pair, vtx_eq, vtx_eq, adj_eq, adj_eq, list5, pc_eq P _ rfl]
        simp only [andB_eq, Bool.and_assoc]
      · rw [blt_false hc']
        simp [andB_eq]
    · rw [blt_false hc]
      simp [andB_eq]
  | .prop k C₁ C₂, b, g => by
    rw [qcOK, qcK, size_lt]
    by_cases hk : k < 12600
    · rw [nb_eq _ hk, vtx_eq, adj_eq, qc_eq C₁, qc_eq C₂]
      simp only [andB_eq, Bool.and_assoc]
    · rw [blt_false hk]
      simp [andB_eq]

theorem strictL_eq : ∀ (L : List Nat) (k : List Nat → Bool), strictL L k = k L
  | [], _ => rfl
  | x :: L, k => by
    change strictB x (fun y => strictL L fun ys => k (y :: ys)) = _
    rw [strictB_eq', strictL_eq L]

theorem q2TreeK_eq (GK GiK : List Nat) (R : Nat) (rs : List (Nat × Nat)) (W : List Nat) :
    q2TreeK GK GiK R rs W = andB (andB (andB (treePts (hsAct GK) 12 oneK rs).2
      (treePts (hisAct GiK) 12 oneK rs).2) (andB (Nat.beq (lenL GK) 12) (invsOK GK GiK)))
      (strictL (conjL R (treePts (hsAct GK) 12 oneK rs).1 (treePts (hisAct GiK) 12 oneK rs).1)
        fun P => andB (distinctK 13 (modL P)) (eqLK P W)) := by
  unfold q2TreeK
  rcases treePts (hsAct GK) 12 oneK rs with ⟨a, b⟩
  rcases treePts (hisAct GiK) 12 oneK rs with ⟨c, d⟩
  rfl

theorem q2TreeK_sound {GK GiK : List Nat} {R : Nat} {rs : List (Nat × Nat)} {W : List Nat}
    (h : q2TreeK GK GiK R rs W = true) : orbChk GK GiK 12 R 13 rs = true ∧ ptsL GK GiK 12 R rs = W := by
  rw [q2TreeK_eq, strictL_eq] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  obtain ⟨h3, h4⟩ := CFSG.KC.TreeK.andB_true h2
  obtain ⟨h5, h6⟩ := CFSG.KC.TreeK.andB_true h1
  obtain ⟨h7, h8⟩ := CFSG.KC.TreeK.andB_true h5
  obtain ⟨h9, h10⟩ := CFSG.KC.TreeK.andB_true h6
  refine ⟨?_, eqLK_sound _ _ h4⟩
  rw [orbChk_eq, h7, h8, h9, h10, h3]
  rfl

theorem gensKb_len {t : Nat} (ht : t < 7) : (gensKb.getD t []).length = 12 := by
  interval_cases t <;> rfl

theorem getL_map0 (f : Nat → Nat) {L : List Nat} {l : Nat} (hl : l < L.length) :
    getL 0 (L.map f) l = f (L.getD l 0) := by
  rw [getL_eq', List.getElem?_map, List.getElem?_eq_getElem hl, List.getD_eq_getElem _ _ hl]
  rfl

theorem gensArr_B {t l : Nat} (ht : t < 7) (hl : l < 12) :
    (gensArr (gensKb.getD t []))[l]! = unpackR 24 (getL 0 (GB t) l) := by
  have hl' : l < (gensKb.getD t []).length := by rw [gensKb_len ht]; exact hl
  rw [GB, getL_map0 _ hl', gensArr, getElem!_pos _ l (by simpa using hl'),
    List.getElem_toArray, List.getElem_map, gEl_eq, ← List.getD_eq_getElem _ 0]

theorem gensInvArr_B {t l : Nat} (ht : t < 7) (hl : l < 12) :
    (gensInvArr (gensKb.getD t []))[l]! = unpackR 24 (getL 0 (GBI t) l) := by
  have hl' : l < (gensKb.getD t []).length := by rw [gensKb_len ht]; exact hl
  rw [GBI, getL_map0 _ hl', gensInvArr, getElem!_pos _ l (by simpa using hl'),
    List.getElem_toArray, List.getElem_map, gElInv_eq, ← List.getD_eq_getElem _ 0]

theorem gensArr_B_size {t : Nat} (ht : t < 7) : (gensArr (gensKb.getD t [])).size = 12 := by
  rw [gensArr, List.size_toArray, List.length_map, gensKb_len ht]

theorem gensArr_BL (t : Nat) : gensArr (gensKb.getD t []) = ((GB t).map (unpackR 24)).toArray := by
  unfold gensArr GB
  rw [List.map_map, List.map_congr_left (fun j _ => gEl_eq j)]
  rfl

theorem repP_eq (t : Nat) : repP (d2Reps.getD t 0) = UP (RBX t, RBXi t) := by
  rw [repP, UP, repX_eq, repXi_eq]
  rfl

theorem root_eq (t : Nat) {m : Nat} (hm : m < 12600) :
    vtxR (nbrX orbE (repP (d2Reps.getD t 0)) m).1 (nbrX orbE (repP (d2Reps.getD t 0)) m).2 =
      unpackR 24 (nbG t m) := by
  rw [repP_eq, nb_eq _ hm, vtx_eq]
  rfl

theorem forest_len {t : Nat} (h : (q2Roots.getD t []).length = (q2Masks.getD t []).length) :
    (q2Forest orbE t).length = (q2Roots.getD t []).length := by
  rw [q2Forest, List.length_map, List.length_zip, h, Nat.min_self]

theorem forest_get {t f : Nat} (h : (q2Roots.getD t []).length = (q2Masks.getD t []).length)
    (hf : f < (q2Roots.getD t []).length) (hm : (q2Roots.getD t []).getD f 0 < 12600) :
    (q2Forest orbE t).getD f default = mkOrbT (gensArr (gensKb.getD t [])) (gensInvArr (gensKb.getD t []))
      (unpackR 24 (nbG t ((q2Roots.getD t []).getD f 0)))
      (treeArr (recs16 ((q2Masks.getD t []).getD f []))) := by
  have hz : f < ((q2Roots.getD t []).zip (q2Masks.getD t [])).length := by
    rw [List.length_zip, ← h, Nat.min_self]; exact hf
  rw [q2Forest, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hz), List.getElem_map,
    List.getElem_zip]
  dsimp only
  rw [← List.getD_eq_getElem _ 0 hf, root_eq t hm, ← List.getD_eq_getElem _ [] (by rw [← h]; exact hf),
    treeOfMasks_eq]
  rfl

theorem q2Tree_sound {t f : Nat} (h : q2Tree t f = true) :
    orbChk (GB t) (GBI t) 12 (nbG t ((q2Roots.getD t []).getD f 0)) 13
        (recs16 ((q2Masks.getD t []).getD f [])) = true ∧
      ptsL (GB t) (GBI t) 12 (nbG t ((q2Roots.getD t []).getD f 0))
        (recs16 ((q2Masks.getD t []).getD f [])) = (MW t f).map (nbG t) :=
  q2TreeK_sound h

theorem mem_MWall {t m : Nat} (h : m ∈ MWall t) : ∃ f < (q2Roots.getD t []).length, m ∈ MW t f := by
  unfold MWall at h
  obtain ⟨f, hf, hm⟩ := List.mem_flatMap.1 h
  exact ⟨f, List.mem_range.1 hf, hm⟩

theorem q2Check_of {t : Nat} (ht : t < 7) (hS : q2SmallK t = true)
    (hT : ∀ f < (q2Roots.getD t []).length, q2Tree t f = true)
    (hL : ∀ c < 197, q2Chunk t c = true) : q2Check t = true := by
  unfold q2SmallK at hS
  obtain ⟨hS1, hS2⟩ := CFSG.KC.TreeK.andB_true hS
  obtain ⟨hS3, hbits⟩ := CFSG.KC.TreeK.andB_true hS1
  obtain ⟨hcent, hlens⟩ := CFSG.KC.TreeK.andB_true hS3
  obtain ⟨hlc, hlm⟩ := CFSG.KC.TreeK.andB_true hlens
  have hlc' := Nat.eq_of_beq_eq_true hlc
  have hlm' := Nat.eq_of_beq_eq_true hlm
  have hbits' := Nat.eq_of_beq_eq_true hbits
  have hz : ∀ i < (q2Roots.getD t []).length, (q2Roots.getD t []).getD i 0 < 12600 ∧
      qcK (RBX t, RBXi t) (nbP (RBX t, RBXi t) ((q2Roots.getD t []).getD i 0))
        ((q2Certs.getD t []).getD i default) = true := by
    intro i hi
    have hzi : i < ((q2Roots.getD t []).zip (q2Certs.getD t [])).length := by
      rw [List.length_zip, ← hlc', Nat.min_self]; exact hi
    have h1 := List.all_eq_true.1 hS2 _ (List.getElem_mem hzi)
    rw [List.getElem_zip] at h1
    obtain ⟨a1, a2⟩ := CFSG.KC.TreeK.andB_true h1
    rw [List.getD_eq_getElem (q2Roots.getD t []) 0 hi,
      List.getD_eq_getElem (q2Certs.getD t []) default (by rw [← hlc']; exact hi)]
    exact ⟨lt_of_blt' a1, a2⟩
  have hG := fun l (hl : l < 12) => gensArr_B ht hl
  have hGi := fun l (hl : l < 12) => gensInvArr_B ht hl
  have hchunk : ∀ c < 197, chunkK 12600 (q2AtK t (MQt t)) c = true := by
    intro c hc
    have h := hL c hc
    unfold q2Chunk at h
    rw [strictB_eq'] at h
    exact h
  have hat := chunks_all (f := q2AtK t (MQt t)) (N := 12600) (nc := 197) (by decide) hchunk
  unfold q2Check
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, hlc'⟩, forest_len hlm'⟩, ?_⟩, ?_⟩
  · rw [repRows_eq]
    exact centOK_of (gensArr_BL t) hcent
  · intro i hi
    obtain ⟨hm, hq⟩ := hz i hi
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [orbE_size']
      exact hm
    · rw [forest_get hlm' hi hm, root_eq t hm]
      exact orbOK_of_chk (gensArr_B_size ht) hG hGi (q2Tree_sound (hT i hi)).1
    · rw [repP_eq, nb_eq _ hm, qc_eq]
      exact hq
  · intro m hm
    rw [orbE_size'] at hm
    have hq := hat m hm
    unfold q2AtK at hq
    rw [root_eq t hm, dcls_eq]
    rcases orB_true hq with e | e
    · rw [← hbits', bit_bitsOf, List.contains_iff_mem] at e
      obtain ⟨f, hf, hmf⟩ := mem_MWall e
      have hfm : f < (q2Forest orbE t).length := by rw [forest_len hlm']; exact hf
      have hroot := (hz f hf).1
      have hc := q2Tree_sound (hT f hf)
      have hmem : (Std.HashSet.ofList ((q2Forest orbE t).flatMap fun o => o.c.pts.toList)).contains
          (unpackR 24 (nbG t m)) = true := by
        rw [Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_flatMap]
        refine ⟨_, List.getElem_mem hfm, ?_⟩
        rw [← List.getD_eq_getElem _ default hfm, forest_get hlm' hf hroot,
          mkOrbT_toList hG hGi (orbChk_walks hc.1).1 (orbChk_walks hc.1).2, hc.2, List.map_map]
        exact List.mem_map_of_mem hmf
      rw [hmem, Bool.or_true]
    · rcases orB_true e with e' | e'
      · rw [Nat.eq_of_beq_eq_true e']
        rfl
      · rw [Nat.eq_of_beq_eq_true e']
        rfl

end CertificateChecks.KernelCo1P

end
