module

public import CFSG.Sporadic.Fi23.Tr.Cert
import all Certificates.Data.CFSGNative.Fi23.Tr
import all CFSG.Sporadic.Fi23.Centralizer
public import CFSG.Sporadic.Fi23.Centralizer

public section

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose, irreducible] noncomputable def trc : TrComp :=
  trCompute orb (dTable orb) (genTables orb (-2)) (pZero ())

@[expose, irreducible] noncomputable def zB : PBits := pZero ()

@[expose, irreducible] noncomputable def cB : PBits := pOf (pZero ()) cData

@[expose, irreducible] noncomputable def tB : PBits := pOf (pZero ()) trData

@[expose, irreducible] noncomputable def lK : Array Table :=
  trLetters orb (dTable orb) (genTables orb (-2))

@[expose, irreducible] noncomputable def tbi : Table := trBi trc.orb

@[expose, irreducible] noncomputable def tdd : Table := trD trc.orb

@[expose, irreducible] noncomputable def phiT : Array Table := trPhi orb trc.orb tdd tbi

theorem zB_eq : zB = pZero () := by unfold zB; rfl
theorem cB_eq : cB = pOf (pZero ()) cData := by unfold cB; rfl
theorem tB_eq : tB = pOf (pZero ()) trData := by unfold tB; rfl
theorem lK_eq : lK = trLetters orb (dTable orb) (genTables orb (-2)) := by unfold lK; rfl
theorem tbi_eq : tbi = trBi trc.orb := by unfold tbi; rfl
theorem tdd_eq : tdd = trD trc.orb := by unfold tdd; rfl
theorem phiT_eq : phiT = trPhi orb trc.orb tdd tbi := by unfold phiT; rfl
theorem phiT_eq' : phiT = trPhi orb trc.orb (trD trc.orb) (trBi trc.orb) := by
  rw [phiT_eq, tdd_eq, tbi_eq]

theorem dT_eq : dT = dTable orb := by
  unfold dT
  exact frozen_eq _

theorem biT_eq : biT = genTables orb (-2) := by
  unfold biT
  exact frozen_eq _

theorem tr_checks :
    trChecks orb (dTable orb) (genTables orb (-2)) (pZero ()) trc 3 = true := by
  unfold trc
  exact tr_certificate

theorem tr_parts :
    trIncOK cData 1080 = true ∧ trIncOK trData 3240 = true ∧ trMemOK cB cData = true ∧
    trMemOK tB trData = true ∧ trStarOK orb dT biT ea phiP cB = true ∧
    trGensOK cB tB lK trc.treeC trc.treeR = true ∧ trCommOK orb dT biT cB trc.cord trc.cpar = true ∧
    trDomOK orb dT biT cB tB trc.domW trc.ncW = true ∧ trCsOK orb dT biT cB tB = true ∧
    trOrbitOK orb.alpha orb.beta zB tB trc.orb 3 = true ∧
    trRowOK orb trc.orb tdd tbi tB trc.rowInv = true ∧
    trFarOK orb trc.orb tdd tbi tB trc.rowInv phiT trc.v0 trc.farTree = true ∧
    trMuOK orb trc.orb tdd tbi trc.rowInv trc.v0 trc.mOrd trc.mPar trc.mWit trc.mH trc.muPos =
      true ∧
    trEdOK orb trc.orb tdd tbi trc.rowInv trc.v0 trc.mOrd trc.edX trc.edK = true := by
  have h := tr_checks
  unfold trChecks at h
  simp only [Bool.and_eq_true] at h
  rw [← phiT_eq', ← tdd_eq, ← tbi_eq, ← lK_eq, ← cB_eq, ← tB_eq, ← zB_eq] at h
  rw [← frozen_eq starPhiPos, ← phiP, ← frozen_eq (dTable orb), ← dT,
    ← frozen_eq (starPts dT), ← ea, ← frozen_eq (genTables orb (-2)), ← biT] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem treeOK_spec' {n r : ℕ} {T : Tree} {letters : Array Table} {lv : Array ℕ}
    (h : Perm.Native.treeOK n r T letters lv = true) :
    0 < T.pts.size ∧ ap T.pts 0 = r ∧ ∀ k < T.pts.size, ap T.pts k < n ∧
      (0 < k → ap T.par k < k ∧ ap T.lab k ∈ lv ∧
        ap letters[ap T.lab k]! (ap T.pts (ap T.par k)) = ap T.pts k) := by
  simp only [Perm.Native.treeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hm, h0⟩, hall⟩ := h
  refine ⟨hm, h0, fun k hk => ?_⟩
  have := (allIn_eq_true.1 hall) k (Nat.zero_le _) hk
  simp only [treeAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.all_eq_true,
    Bool.or_eq_true, Array.contains_iff_mem] at this
  obtain ⟨⟨⟨hlt, -⟩, -⟩, hpar⟩ := this
  refine ⟨hlt, fun hk0 => ?_⟩
  rcases hpar with h | ⟨⟨h1, h2⟩, h3⟩
  · omega
  · exact ⟨h1, h2, h3⟩

theorem pMaps_spec {T : Table} {A B : PBits} (h : pMaps T A B = true) {x : ℕ} (hx : x < 31671) :
    pBit B (ap T x) = pBit A x := by
  have := allIn_eq_true.1 h x (Nat.zero_le _) hx
  simpa using this

theorem trIncOK_spec {S : Array ℕ} {n : ℕ} (h : trIncOK S n = true) :
    S.size = n ∧ (∀ k < n - 1, S[k]! < S[k + 1]!) ∧ S[n - 1]! < 31671 := by
  unfold trIncOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun k hk => ?_, h3⟩
  have := allIn_eq_true.1 h2 k (Nat.zero_le _) hk
  simpa using this

theorem trMemOK_spec {B : PBits} {S : Array ℕ} (h : trMemOK B S = true) {x : ℕ}
    (hx : x < 31671) : pBit B x = S.contains x := by
  have := allIn_eq_true.1 h x (Nat.zero_le _) hx
  simpa using this

theorem trStarOK_spec {O : WOrbit} {D bi : Table} {ea phiP : Array ℕ} {cB : PBits}
    (h : trStarOK O D bi ea phiP cB = true) :
    failC < 31671 ∧ failC ≠ 0 ∧ ap D failC ≠ failC ∧ ∀ u < 3510,
      pBit cB ea[phiP[u]!]! = Fi22.Native.lhData[0]!.contains u ∧
      (Fi22.Native.lhData[1]!.contains u = true ↔
        tauAct O D bi failC ea[phiP[u]!]! = ea[phiP[u]!]!) := by
  unfold trStarOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun u hu => ?_⟩
  have := allIn_eq_true.1 h4 u (Nat.zero_le _) hu
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨a1, a2⟩ := this
  refine ⟨a1, ?_⟩
  rw [a2]
  simp

theorem cGens_size : cGens.size = 9 := rfl

theorem xiGens_size : xiGens.size = 10 := rfl

theorem trGensOK_spec {cB tB : PBits} {letters : Array Table} {treeC treeR : Tree}
    (h : trGensOK cB tB letters treeC treeR = true) :
    letters.size = 9 ∧ (∀ l < 9, cGens[l]! < 31671 ∧ pBit cB cGens[l]! = true ∧
      pMaps letters[l]! cB cB = true) ∧
      Perm.Native.treeOK 31671 0 treeC letters (Array.range 9) = true ∧
      Perm.Native.treeOK 31671 rRoot treeR letters (Array.range 9) = true ∧
      ∀ x < 31671, (pBit cB x = true → inTreeB treeC x = true) ∧
        (pBit tB x = true → pBit cB x = false → inTreeB treeR x = true) ∧
        (pBit cB x = true → pBit tB x = true) := by
  unfold trGensOK at h
  rw [cGens_size] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun l hl => ?_, h3, h4, fun x hx => ?_⟩
  · have := allIn_eq_true.1 h2 l (Nat.zero_le _) hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨a1, a2⟩, a3⟩ := this
    exact ⟨a1, a2, a3⟩
  · have := allIn_eq_true.1 h5 x (Nat.zero_le _) hx
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
    obtain ⟨⟨a1, a2⟩, a3⟩ := this
    refine ⟨fun hc => ?_, fun ht hc => ?_, fun hc => ?_⟩
    · rcases a1 with a | a
      · rw [hc] at a; exact absurd a (by decide)
      · exact a
    · rcases a2 with (a | a) | a
      · rw [ht] at a; exact absurd a (by decide)
      · rw [hc] at a; exact absurd a (by decide)
      · exact a
    · rcases a3 with a | a
      · rw [hc] at a; exact absurd a (by decide)
      · exact a

theorem trCommOK_spec {O : WOrbit} {D bi : Table} {cB : PBits} {ord par : Array ℕ}
    (h : trCommOK O D bi cB ord par = true) :
    ord.size = 1080 ∧ par.size = 1080 ∧ ord[0]! = 0 ∧ pBit cB 0 = true ∧
      (∀ k, 1 ≤ k → k < 1080 → par[k]! < k ∧ ord[k]! < 31671 ∧ pBit cB ord[k]! = true ∧
        tauAct O D bi ord[par[k]!]! ord[k]! = ord[k]! ∧ ord[par[k]!]! ≠ ord[k]!) ∧
      ∀ x ∈ cData, x ∈ ord := by
  unfold trCommOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h0⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h0, fun k hk1 hk => ?_, fun x hx => ?_⟩
  · have := allIn_eq_true.1 h4 k hk1 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at this
    obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := this
    exact ⟨a1, a2, a3, a4, a5⟩
  · obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
    have := h5 k hk
    simpa using this

theorem trDomOK_spec {O : WOrbit} {D bi : Table} {cB tB : PBits} {domW ncW : Array ℕ}
    (h : trDomOK O D bi cB tB domW ncW = true) {f : ℕ} (hf : f < 31671)
    (hfT : pBit tB f = false) :
    domW[f]! < 31671 ∧ pBit cB domW[f]! = true ∧ tauAct O D bi domW[f]! f = f ∧
      ncW[f]! < 31671 ∧ pBit tB ncW[f]! = true ∧ tauAct O D bi ncW[f]! f ≠ f := by
  have := allIn_eq_true.1 h f (Nat.zero_le _) hf
  simp only [hfT, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
    ne_eq] at this
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := this
  exact ⟨a1, a2, a3, a4, a5, a6⟩

theorem trCsOK_spec {O : WOrbit} {D bi : Table} {cB tB : PBits} (h : trCsOK O D bi cB tB = true) :
    csV ≠ csW ∧ csV < 31671 ∧ csW < 31671 ∧ pBit tB csV = true ∧ pBit cB csV = false ∧
      pBit tB csW = true ∧ pBit cB csW = false ∧
      ∀ y < 31671, pBit cB (tauAct O D bi csV y) = pBit cB (tauAct O D bi csW y) := by
  unfold trCsOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun y hy => ?_⟩
  have := allIn_eq_true.1 h8 y (Nat.zero_le _) hy
  simpa using this

theorem trOrbitOK_spec {alpha beta : Table} {z tB : PBits} {o : TrOrb} {chunks : ℕ}
    (h : trOrbitOK alpha beta z tB o chunks = true) :
    o.sets.size = 137632 ∧ o.pa.size = 137632 ∧ o.pb.size = 137632 ∧ o.par.size = 137632 ∧
      o.lab.size = 137632 ∧ (∀ x < 31671, pBit o.sets[0]! x = pBit tB x) ∧
      (∀ k < 137632, ap o.pa k < 137632 ∧ ap o.pb k < 137632 ∧
        pMaps alpha o.sets[k]! o.sets[ap o.pa k]! = true ∧
        pMaps beta o.sets[k]! o.sets[ap o.pb k]! = true) ∧
      (∀ k, 1 ≤ k → k < 137632 → ap o.par k < k ∧
        ((ap o.lab k = 1 ∧ ap o.pa (ap o.par k) = k) ∨
          (ap o.lab k = 2 ∧ ap o.pb (ap o.par k) = k))) ∧
      ∀ k < 137632, trFind o z o.sets[k]! = k := by
  unfold trOrbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun x hx => ?_, fun k hk => ?_, fun k hk1 hk => ?_, fun k hk => ?_⟩
  · have := allIn_eq_true.1 h6 x (Nat.zero_le _) hx
    simpa using this
  · have := parAll_eq_true h7 k hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := this
    exact ⟨a1, a2, a3, a4⟩
  · have := allIn_eq_true.1 h8 k hk1 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at this
    exact this
  · have := parAll_eq_true h9 k hk
    simpa using this

theorem trRowOK_spec {O : WOrbit} {o : TrOrb} {D bi : Table} {tB : PBits} {rowInv : Table}
    (h : trRowOK O o D bi tB rowInv = true) :
    rowInv.size = 137632 ∧
      (∀ f < 31671, pBit tB f = false → trAct O o D bi f 0 ≠ 0 ∧
        ap rowInv (trAct O o D bi f 0) = f) ∧
      ∀ m < 137632, rowInv[m]! = none32 ∨ (ap rowInv m < 31671 ∧ pBit tB (ap rowInv m) = false ∧
        trAct O o D bi (ap rowInv m) 0 = m) := by
  unfold trRowOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun f hf hfT => ?_, fun m hm => ?_⟩
  · have := allIn_eq_true.1 h2 f (Nat.zero_le _) hf
    simp only [hfT, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
    exact this
  · have := allIn_eq_true.1 h3 m (Nat.zero_le _) hm
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at this
    rcases this with a | ⟨⟨a1, a2⟩, a3⟩
    · exact Or.inl a
    · exact Or.inr ⟨a1, a2, a3⟩

theorem trIsFar_iff {rowInv : Table} {m : ℕ} :
    trIsFar rowInv m = true ↔ m ≠ 0 ∧ rowInv[m]! = none32 := by
  unfold trIsFar
  simp

theorem trFarOK_spec {O : WOrbit} {o : TrOrb} {D bi : Table} {tB : PBits} {rowInv : Table}
    {phi : Array Table} {v0 : ℕ} {tr : Tree}
    (h : trFarOK O o D bi tB rowInv phi v0 tr = true) :
    (∀ l < 10, xiGens[l]! < 31671 ∧ pBit tB xiGens[l]! = true ∧
      trAct O o D bi xiGens[l]! 0 = 0) ∧ v0 < 137632 ∧ trIsFar rowInv v0 = true ∧
      Perm.Native.treeOK 137632 v0 tr phi (Array.range 10) = true ∧
      ∀ m < 137632, trIsFar rowInv m = true → inTreeB tr m = true := by
  unfold trFarOK at h
  rw [xiGens_size] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun l hl => ?_, h2, h3, h4, fun m hm hf => ?_⟩
  · have := allIn_eq_true.1 h1 l (Nat.zero_le _) hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    obtain ⟨⟨a1, a2⟩, a3⟩ := this
    exact ⟨a1, a2, a3⟩
  · have := allIn_eq_true.1 h5 m (Nat.zero_le _) hm
    simpa [hf] using this

theorem trMuOK_spec {O : WOrbit} {o : TrOrb} {D bi : Table} {rowInv : Table} {v0 : ℕ}
    {mOrd mPar mWit mH : Array ℕ} {muPos : Table}
    (h : trMuOK O o D bi rowInv v0 mOrd mPar mWit mH muPos = true) :
    0 < mOrd.size ∧
      (∀ k < mOrd.size, mOrd[k]! < 137632 ∧ rowInv[mOrd[k]!]! ≠ none32 ∧ mH[k]! < 31671 ∧
        pBit o.sets[v0]! mH[k]! = false ∧ trAct O o D bi mH[k]! v0 = mOrd[k]! ∧
        ap muPos mOrd[k]! = k) ∧
      (∀ k, 1 ≤ k → k < mOrd.size → mPar[k]! < k ∧ mWit[k]! < 31671 ∧
        pBit o.sets[mOrd[mPar[k]!]!]! mWit[k]! = false ∧
        trAct O o D bi mWit[k]! mOrd[mPar[k]!]! = mOrd[k]!) ∧
      ∀ h < 31671, pBit o.sets[v0]! h = false → rowInv[trAct O o D bi h v0]! ≠ none32 →
        ap muPos (trAct O o D bi h v0) < mOrd.size ∧
          mOrd[ap muPos (trAct O o D bi h v0)]! = trAct O o D bi h v0 := by
  unfold trMuOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, fun k hk => ?_, fun k hk1 hk => ?_, fun x hx hxV hxR => ?_⟩
  · have := allIn_eq_true.1 h6 k (Nat.zero_le _) hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
      beq_iff_eq] at this
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := this
    exact ⟨a1, a2, a3, a4, a5, a6⟩
  · have := allIn_eq_true.1 h7 k hk1 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at this
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := this
    exact ⟨a1, a2, a3, a4⟩
  · have := allIn_eq_true.1 h8 x (Nat.zero_le _) hx
    simp only [hxV, Bool.false_or, Bool.or_eq_true, beq_iff_eq, hxR, false_or,
      Bool.and_eq_true, decide_eq_true_eq] at this
    exact this

theorem trEdOK_spec {O : WOrbit} {o : TrOrb} {D bi : Table} {rowInv : Table} {v0 : ℕ}
    {mOrd edX edK : Array ℕ} (h : trEdOK O o D bi rowInv v0 mOrd edX edK = true) {f : ℕ}
    (hf : f < 31671) (hfV : pBit o.sets[v0]! f = false)
    (hfar : trIsFar rowInv (trAct O o D bi f v0) = true) :
    edX[f]! < mOrd.size ∧ edK[f]! < 31671 ∧ pBit o.sets[mOrd[edX[f]!]!]! edK[f]! = false ∧
      trAct O o D bi edK[f]! mOrd[edX[f]!]! = trAct O o D bi f v0 := by
  unfold trEdOK at h
  dsimp only at h
  have := allIn_eq_true.1 h f (Nat.zero_le _) hf
  simp only [hfV, hfar, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_iff_eq] at this
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := this
  exact ⟨a1, a2, a3, a4⟩

end CFSG.Sporadic.Fi23
