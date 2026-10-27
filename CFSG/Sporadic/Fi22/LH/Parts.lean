module

public import CFSG.Sporadic.Fi22.LH.Cert
public import CFSG.Sporadic.Fi22.Setup

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.F4.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose, irreducible] noncomputable def tT : Array Table := tauAll orb

@[expose, irreducible] noncomputable def lhc : LHComp := lhCompute orb tT

theorem lh_checks : lhChecks orb tT lhc = true := by
  unfold lhc tT
  exact lh_certificate

theorem lh_parts :
    tT.size = 3510 ∧ dataOK lhData = true ∧ lhc.B.size = 2 ∧ lhc.orb.size = 2 ∧
    lhc.keys.size = 2 ∧ lhc.letters.size = 2 ∧ lhc.trees.size = 2 ∧ lhc.cord.size = 2 ∧
    lhc.cpar.size = 2 ∧
    (∀ i < 2, memOK lhc.B[i]! lhData[i]! = true ∧ closedOK tT lhc.B[i]! = true ∧
      starOK (eaPts orb) lhc.B[i]! (2 * i) = true ∧
      rootTreeOK tT lhData[i]! lhc.letters[i]! lhc.trees[i]! = true ∧
      commTreeOK tT lhData[i]! lhc.B[i]! lhc.cord[i]! lhc.cpar[i]! = true ∧
      domOK tT lhc.B[i]! = true ∧
      Native.orbitOK orb.alpha orb.beta lhc.B[i]! lhc.orb[i]! lhc.keys[i]! = true) ∧
    count63OK tT lhc.B[0]! = true ∧ failOK tT (ePos (eaPts orb)) = true ∧
    keyFind lhc.keys[0]! lhc.B[1]! = 14080 ∧
    swapOK (lhUTab orb) lhc.B[0]! lhc.B[1]! lhc.orb[0]! lhc.orb[1]! lhc.uIdx = true ∧
    rowOK tT lhc.B[0]! lhc.orb[0]! lhc.rowR lhc.rowInv = true ∧
    phiOK tT lhc.B[0]! lhc.orb[0]! lhc.phi = true ∧
    farOK lhc.rowInv lhc.phi lhc.v0 lhc.farTree = true ∧
    muOK tT lhc.B[0]! lhc.orb[0]! lhc.rowR lhc.muW lhc.mOrd lhc.mPar lhc.mWit lhc.v0 = true ∧
    edOK tT lhc.B[0]! lhc.orb[0]! lhc.rowR lhc.rowInv lhc.muW lhc.edW lhc.edF lhc.edK
      lhc.v0 = true := by
  have h := lh_checks
  unfold lhChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun i hi => ?_, h11, h12, h13, h14, h15, h16, h17,
    h18, h19⟩
  have := allIn_eq_true.1 h10 i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, and_assoc] at this
  exact this

theorem anyBelow_eq_true {n : ℕ} {p : ℕ → Bool} : anyBelow n p = true ↔ ∃ x < n, p x = true := by
  unfold anyBelow
  simp [List.any_eq_true]

theorem dataOK_spec {L : Array (Array ℕ)} (h : dataOK L = true) :
    L.size = 2 ∧ ∀ i < 2, (L[i]!).size = 351 ∧ (L[i]!)[0]! = 0 ∧
      (∀ k < 350, (L[i]!)[k]! < (L[i]!)[k + 1]!) ∧ (L[i]!)[350]! < 3510 := by
  unfold dataOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hs, hall⟩ := h
  refine ⟨hs, fun i hi => ?_⟩
  have := hall i (by omega)
  rw [getElem!_pos L i (by omega)]
  obtain ⟨h1, h2, h3, h4⟩ := this
  refine ⟨h1, h2, fun k hk => ?_, h4⟩
  have := allIn_eq_true.1 h3 k (Nat.zero_le _) hk
  simpa using this

theorem memOK_spec {B : Bits} {S : Array ℕ} (h : memOK B S = true) {x : ℕ} (hx : x < 3510) :
    bitAt B x = S.contains x := by
  have := allIn_eq_true.1 h x (Nat.zero_le _) hx
  simpa using this

theorem closedOK_spec {T : Array Table} {B : Bits} (h : closedOK T B = true) {s t : ℕ}
    (hs : s < 3510) (ht : t < 3510) (hBs : bitAt B s = true) (hBt : bitAt B t = true) :
    bitAt B (ap T[s]! t) = true := by
  have h1 := allIn_eq_true.1 h s (Nat.zero_le _) hs
  simp only [hBs, Bool.not_true, Bool.false_or] at h1
  have h2 := allIn_eq_true.1 h1 t (Nat.zero_le _) ht
  simpa [hBt] using h2

theorem starOK_spec {ea : Array ℕ} {B : Bits} {j : ℕ} (h : starOK ea B j = true) {u : ℕ}
    (hu : u < 693) : bitAt B ea[phiPos[u]!]! = hypC j uPts[u]! := by
  have := allIn_eq_true.1 h u (Nat.zero_le _) hu
  simpa using this

theorem rootTreeOK_spec {T : Array Table} {S : Array ℕ} {letters : Array Table} {tr : Tree}
    (h : rootTreeOK T S letters tr = true) :
    letters.size = 351 ∧ (∀ l < 351, letters[l]! = T[S[l]!]!) ∧
      Perm.Native.treeOK 3510 0 tr letters (Array.range 351) = true ∧
      ∀ x ∈ S, ap tr.pos x < tr.pts.size ∧ ap tr.pts (ap tr.pos x) = x := by
  unfold rootTreeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun l hl => ?_, h3, fun x hx => ?_⟩
  · have := allIn_eq_true.1 h2 l (Nat.zero_le _) hl
    simpa using this
  · obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
    exact h4 k hk

theorem commTreeOK_spec {T : Array Table} {S : Array ℕ} {B : Bits} {ord par : Array ℕ}
    (h : commTreeOK T S B ord par = true) :
    ord.size = 351 ∧ par.size = 351 ∧ ord[0]! = 0 ∧
      (∀ k, 1 ≤ k → k < 351 → par[k]! < k ∧ bitAt B ord[k]! = true ∧
        ap T[ord[par[k]!]!]! ord[k]! = ord[k]! ∧ ord[par[k]!]! ≠ ord[k]!) ∧
      ∀ x ∈ S, x ∈ ord := by
  unfold commTreeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, fun k hk1 hk => ?_, fun x hx => ?_⟩
  · have := allIn_eq_true.1 h4 k hk1 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, and_assoc] at this
    exact this
  · obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
    have := h5 k hk
    simpa using this

theorem domOK_spec {T : Array Table} {B : Bits} (h : domOK T B = true) {f : ℕ} (hf : f < 3510)
    (hfB : bitAt B f = false) :
    (∃ x < 3510, bitAt B x = true ∧ ap T[f]! x = x) ∧
      ∃ x < 3510, bitAt B x = true ∧ ap T[f]! x ≠ x := by
  have := allIn_eq_true.1 h f (Nat.zero_le _) hf
  simp only [hfB, Bool.false_or, Bool.and_eq_true, anyBelow_eq_true, beq_iff_eq,
    bne_iff_ne] at this
  exact this

theorem count63OK_spec {T : Array Table} {B : Bits} (h : count63OK T B = true) {f : ℕ}
    (hf : f < 3510) (hfB : bitAt B f = false) :
    (List.range 3510).countP (fun x => bitAt B x && ap T[f]! x == x) = 63 := by
  have := allIn_eq_true.1 h f (Nat.zero_le _) hf
  simpa [hfB] using this

theorem failOK_spec {T : Array Table} {ep : Array ℕ} (h : failOK T ep = true) :
    ep[63]! < 693 ∧ hypC 1 uPts[phiData[ep[63]!]!]! = true ∧ ap T[63]! 2751 = 2751 ∧
      ap T[0]! 2751 ≠ 2751 ∧
      ∀ x < 3510, (ep[x]! < 693 ∧ hypC 1 uPts[phiData[ep[x]!]!]! = true ∧ ap T[63]! x = x ∧
        x ≠ 63) ↔ (ap T[63]! x = x ∧ x ≠ 63 ∧ ap T[0]! x = x ∧ x ≠ 0 ∧ ap T[2751]! x = x ∧
          x ≠ 2751) := by
  unfold failOK lhFailT lhFailC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, and_assoc] at h
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h5, fun x hx => ?_⟩
  have := allIn_eq_true.1 h6 x (Nat.zero_le _) hx
  rw [beq_iff_eq, Bool.eq_iff_iff] at this
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, and_assoc] at this
  exact this

theorem orbitOK_spec {alpha beta : Table} {B : Bits} {o : LHOrb} {K : Std.HashMap (List ℕ) ℕ}
    (h : CFSG.Sporadic.Fi22.Native.orbitOK alpha beta B o K = true) :
    o.sets.size = 14080 ∧ o.pa.size = 14080 ∧ o.pb.size = 14080 ∧ o.par.size = 14080 ∧
      o.lab.size = 14080 ∧ (∀ x < 3510, bitAt o.sets[0]! x = bitAt B x) ∧
      (∀ k < 14080, o.pa[k]! < 14080 ∧ o.pb[k]! < 14080 ∧
        mapsOnto alpha o.sets[k]! o.sets[o.pa[k]!]! = true ∧
        mapsOnto beta o.sets[k]! o.sets[o.pb[k]!]! = true) ∧
      (∀ k, 1 ≤ k → k < 14080 → o.par[k]! < k ∧
        ((o.lab[k]! = 1 ∧ o.pa[o.par[k]!]! = k) ∨ (o.lab[k]! = 2 ∧ o.pb[o.par[k]!]! = k))) ∧
      ∀ k < 14080, keyFind K o.sets[k]! = k := by
  unfold CFSG.Sporadic.Fi22.Native.orbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun x hx => ?_, fun k hk => ?_, fun k hk1 hk => ?_,
    fun k hk => ?_⟩
  · have := allIn_eq_true.1 h6 x (Nat.zero_le _) hx
    simpa using this
  · have := parAll_eq_true h7 k hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at this
    exact this
  · have := allIn_eq_true.1 h8 k hk1 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at this
    exact this
  · have := parAll_eq_true h9 k hk
    simpa using this

theorem swapOK_spec {U : Table} {B0 B1 : Bits} {o0 o1 : LHOrb} {uIdx : Array ℕ}
    (h : swapOK U B0 B1 o0 o1 uIdx = true) :
    uIdx[0]! < 14080 ∧ mapsOnto U B0 o1.sets[uIdx[0]!]! = true ∧ uIdx[1]! < 14080 ∧
      mapsOnto U B1 o0.sets[uIdx[1]!]! = true := by
  unfold swapOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, h2, h3, h4, h5⟩ := h
  exact ⟨h2, h3, h4, h5⟩

theorem rowOK_spec {T : Array Table} {B0 : Bits} {o0 : LHOrb} {rowR rowInv : Array ℕ}
    (h : rowOK T B0 o0 rowR rowInv = true) :
    rowR.size = 3510 ∧ rowInv.size = 14080 ∧
      (∀ f < 3510, bitAt B0 f = false → rowR[f]! < 14080 ∧ rowR[f]! ≠ 0 ∧
        mapsOnto T[f]! B0 o0.sets[rowR[f]!]! = true ∧ rowInv[rowR[f]!]! = f) ∧
      ∀ m < 14080, rowInv[m]! = 3510 ∨
        (rowInv[m]! < 3510 ∧ bitAt B0 rowInv[m]! = false ∧ rowR[rowInv[m]!]! = m) := by
  unfold rowOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun f hf hfB => ?_, fun m hm => ?_⟩
  · have := allIn_eq_true.1 h3 f (Nat.zero_le _) hf
    simp only [hfB, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
      beq_iff_eq, and_assoc] at this
    exact this
  · have := allIn_eq_true.1 h4 m (Nat.zero_le _) hm
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', and_assoc] at this
    exact this

theorem phiOK_spec {T : Array Table} {B0 : Bits} {o0 : LHOrb} {phi : Array Table}
    (h : phiOK T B0 o0 phi = true) :
    phi.size = xiGens.size ∧ ∀ l < xiGens.size, xiGens[l]! < 3510 ∧ bitAt B0 xiGens[l]! = true ∧
      phi[l]!.size = 14080 ∧ ∀ m < 14080, ap phi[l]! m < 14080 ∧
        mapsOnto T[xiGens[l]!]! o0.sets[m]! o0.sets[ap phi[l]! m]! = true := by
  unfold phiOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun l hl => ?_⟩
  have := allIn_eq_true.1 h2 l (Nat.zero_le _) hl
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at this
  obtain ⟨a1, a2, a3, a4⟩ := this
  refine ⟨a1, a2, a3, fun m hm => ?_⟩
  have := parAll_eq_true a4 m hm
  simpa using this

theorem farOK_spec {rowInv : Array ℕ} {phi : Array Table} {v0 : ℕ} {tr : Tree}
    (h : farOK rowInv phi v0 tr = true) :
    v0 < 14080 ∧ isFar rowInv v0 = true ∧
      Perm.Native.treeOK 14080 v0 tr phi (Array.range xiGens.size) = true ∧
      ∀ m < 14080, isFar rowInv m = true →
        ap tr.pos m < tr.pts.size ∧ ap tr.pts (ap tr.pos m) = m := by
  unfold farOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun m hm hfar => ?_⟩
  have := allIn_eq_true.1 h4 m (Nat.zero_le _) hm
  simpa [hfar] using this

theorem muOK_spec {T : Array Table} {B0 : Bits} {o0 : LHOrb} {rowR muW mOrd mPar mWit : Array ℕ}
    {v0 : ℕ} (h : muOK T B0 o0 rowR muW mOrd mPar mWit v0 = true) :
    muW.size = 3510 ∧
      (∀ f < 3510, bitAt B0 f = false → muW[f]! < 3510 →
        bitAt o0.sets[rowR[f]!]! muW[f]! = false ∧
        mapsOnto T[muW[f]!]! o0.sets[rowR[f]!]! o0.sets[v0]! = true) ∧
      (∀ f < 3510, bitAt B0 f = false → ¬ muW[f]! < 3510 →
        commonCount o0.sets[rowR[f]!]! o0.sets[v0]! ≠ 63) ∧
      0 < mOrd.size ∧ mPar.size = mOrd.size ∧ mWit.size = mOrd.size ∧
      (∀ k < mOrd.size, mOrd[k]! < 3510 ∧ bitAt B0 mOrd[k]! = false ∧ muW[mOrd[k]!]! < 3510) ∧
      (∀ k, 1 ≤ k → k < mOrd.size → mPar[k]! < k ∧ mWit[k]! < 3510 ∧
        bitAt o0.sets[rowR[mOrd[mPar[k]!]!]!]! mWit[k]! = false ∧
        mapsOnto T[mWit[k]!]! o0.sets[rowR[mOrd[mPar[k]!]!]!]! o0.sets[rowR[mOrd[k]!]!]! =
          true) ∧
      ∀ f < 3510, bitAt B0 f = false → muW[f]! ≠ 3510 → f ∈ mOrd := by
  unfold muOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, fun f hf hfB hw => ?_, fun f hf hfB hw => ?_, h3, h4, h5, fun k hk => ?_,
    fun k hk1 hk => ?_, fun f hf hfB hw => ?_⟩
  · have := allIn_eq_true.1 h2 f (Nat.zero_le _) hf
    simp only [hfB, Bool.false_or, hw, ite_true, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this
  · have := allIn_eq_true.1 h2 f (Nat.zero_le _) hf
    simp only [hfB, Bool.false_or, hw, ite_false, bne_iff_ne] at this
    exact this
  · have := allIn_eq_true.1 h6 k (Nat.zero_le _) hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_assoc] at this
    exact this
  · have := allIn_eq_true.1 h7 k hk1 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_assoc] at this
    exact this
  · have := allIn_eq_true.1 h8 f (Nat.zero_le _) hf
    simp only [hfB, Bool.false_or, Bool.or_eq_true, beq_iff_eq, hw, false_or,
      Array.contains_iff_mem] at this
    exact this

theorem edOK_spec {T : Array Table} {B0 : Bits} {o0 : LHOrb}
    {rowR rowInv muW edW edF edK : Array ℕ} {v0 : ℕ}
    (h : edOK T B0 o0 rowR rowInv muW edW edF edK v0 = true) {f : ℕ} (hf : f < 3510)
    (hfV : bitAt o0.sets[v0]! f = false) :
    edW[f]! < 14080 ∧ mapsOnto T[f]! o0.sets[v0]! o0.sets[edW[f]!]! = true ∧
      (isFar rowInv edW[f]! = true → edF[f]! < 3510 ∧ bitAt B0 edF[f]! = false ∧
        muW[edF[f]!]! < 3510 ∧ edK[f]! < 3510 ∧
        bitAt o0.sets[rowR[edF[f]!]!]! edK[f]! = false ∧
        mapsOnto T[edK[f]!]! o0.sets[rowR[edF[f]!]!]! o0.sets[edW[f]!]! = true) := by
  unfold edOK at h
  have := allIn_eq_true.1 h f (Nat.zero_le _) hf
  simp only [hfV, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', and_assoc] at this
  obtain ⟨a1, a2, a3⟩ := this
  refine ⟨a1, a2, fun hfar => ?_⟩
  rcases a3 with h' | h'
  · rw [hfar] at h'
    exact absurd h' (by decide)
  · exact h'

end CFSG.Sporadic.Fi22
