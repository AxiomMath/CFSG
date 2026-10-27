module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestCert
public import CFSG.LocalAnalysis.StandardType.GGQ2S08SgnLin

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {n : ℕ}

@[expose] def reflCertB (gens : List (Vn n × Vn n)) (L : List ((Vn n × Vn n) × List ℕ × ℕ)) :
    Bool :=
  L.all fun q => decide (q.2.2 < gens.length) && decide (q.1.2 ⬝ᵥ q.1.1 = 2) &&
    sameRefl (wConj gens q.2.1 (letAt gens q.2.2)) q.1

theorem mem_of_reflCertB {gens : List (Vn n × Vn n)} (hgens : AlphOK gens)
    {W : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} (hgW : ∀ l ∈ gens, letLin l ∈ W)
    {L : List ((Vn n × Vn n) × List ℕ × ℕ)} (hL : reflCertB gens L = true)
    {l : Vn n × Vn n} (hl : l ∈ L.map Prod.fst) : letLin l ∈ W := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
  have h := List.all_eq_true.mp hL q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hk, hq2⟩, hsame⟩ := h
  have hgk : letAt gens q.2.2 ∈ gens := by
    unfold letAt
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  obtain ⟨h', hconj⟩ := wLin_conj hgens q.2.1 (letAt gens q.2.2) (hgens _ hgk)
  rw [letLin_of _ hq2, ← refl_eq_of_sameRefl hsame h' hq2, ← hconj]
  refine W.mul_mem (W.mul_mem (wLin_mem hgW _) ?_) (W.inv_mem (wLin_mem hgW _))
  rw [← letLin_of _ (hgens _ hgk)]
  exact hgW _ hgk

variable {r : ℕ}

@[expose] def sgnDiffL (i j : Fin r) : Vn (r + 1) × Vn (r + 1) :=
  (Pi.single i.castSucc 1 - Pi.single j.castSucc 1, Pi.single i.castSucc 1 - Pi.single j.castSucc 1)

@[expose] def sgnSumL (i j : Fin r) : Vn (r + 1) × Vn (r + 1) :=
  (frameE r i + frameE r j, frameE r i + frameE r j)

@[expose] def sgnFlipL (i : Fin r) : Vn (r + 1) × Vn (r + 1) :=
  (frameE r i, (2 : ZMod 3) • frameE r i)

theorem sgnDiff_eq_letLin (i j : Fin r) (h : i ≠ j) : sgnDiff i j h = letLin (sgnDiffL i j) := by
  rw [letLin_of]
  rfl

theorem sgnSum_eq_letLin (i j : Fin r) (h : i ≠ j) : sgnSum i j h = letLin (sgnSumL i j) := by
  rw [letLin_of]
  rfl

theorem sgnFlip_eq_letLin (i : Fin r) : sgnFlip i = letLin (sgnFlipL i) := by
  rw [letLin_of]
  rfl

@[expose] def bFrameB (r : ℕ) (L : List ((Vn (r + 1) × Vn (r + 1)) × List ℕ × ℕ)) : Bool :=
  decide (∀ i j : Fin r, i ≠ j → sgnDiffL i j ∈ L.map Prod.fst ∧ sgnSumL i j ∈ L.map Prod.fst) &&
    decide (∀ i : Fin r, sgnFlipL i ∈ L.map Prod.fst)

@[expose] def movesB (x : Vn n) (c a : Vn n) : Bool :=
  !pmB x (letApp (c, a) x)

@[expose] def bCovB (r : ℕ) (pats : List ((Vn (r + 1) × Vn (r + 1)) × PatV (r + 1))) : Bool :=
  (List.range (r + 1)).all fun k => [0, 1, 2].all fun l => [0, 1, 2].all fun g =>
    [0, 1, 2].all fun d =>
      !(decide (canonA r k l d ⬝ᵥ canonC r k g = 2) && movesB (xLast r) (canonC r k g) (canonA r k l d))
        || decide ((canonC r k g, canonA r k l d) ∈ pats.map Prod.fst)

theorem zmod3_mem_list (t : ZMod 3) : t ∈ ([0, 1, 2] : List (ZMod 3)) := by
  revert t
  decide

theorem movesB_of_conj {x : Vn n} {u w : Vn n ≃ₗ[ZMod 3] Vn n} (hwx : w x = x)
    (hux : ¬ FixesLine x u) {c a : Vn n} (h : a ⬝ᵥ c = 2) (hconj : w * u * w⁻¹ = refl c a h) :
    movesB x c a = true := by
  unfold movesB pmB
  rw [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
  have hwx' : w⁻¹ x = x := by
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq]
    exact hwx.symm
  have hval : letApp (c, a) x = w (u x) := by
    have := congrArg (fun T : Vn n ≃ₗ[ZMod 3] Vn n => T x) hconj
    simp only [LinearEquiv.mul_apply, hwx', refl_apply] at this
    exact this.symm
  have hws : w.symm x = x := by
    rw [LinearEquiv.symm_apply_eq]
    exact hwx.symm
  rw [hval]
  constructor
  · intro h1
    apply hux
    left
    have := congrArg w.symm h1
    rw [LinearEquiv.symm_apply_apply, hws] at this
    exact this
  · intro h1
    apply hux
    right
    have := congrArg w.symm h1
    rw [LinearEquiv.symm_apply_apply, map_neg, hws] at this
    exact this

variable {W A M : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1))}

theorem TestHyp.bframe_cover (hT : TestHyp W (xLast r) A M)
    (hW : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum i j h ∈ W) (hWf : ∀ i : Fin r, sgnFlip i ∈ W)
    {pats : List ((Vn (r + 1) × Vn (r + 1)) × PatV (r + 1))} (hcov : bCovB r pats = true) :
    ∀ u ∈ A, IsRefl u → ¬ FixesLine (xLast r) u → ∃ w ∈ W, ∃ p ∈ pats,
      ∃ h : p.1.2 ⬝ᵥ p.1.1 = 2, w * u * w⁻¹ = refl p.1.1 p.1.2 h := by
  intro u hu huR hux
  obtain ⟨w, hw, k, l, g, d, h, -, hkr, hwx, hconj⟩ := hT.exists_canonical_B hW hWs hWf hu huR hux
  have hmv := movesB_of_conj hwx hux h hconj
  have hc := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    hcov k (List.mem_range.mpr (by omega))) l (zmod3_mem_list l)) g (zmod3_mem_list g)) d
    (zmod3_mem_list d)
  rw [show decide (canonA r k l d ⬝ᵥ canonC r k g = 2) = true from decide_eq_true h, hmv,
    Bool.and_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
  obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hc
  have hp2 : p.1.2 ⬝ᵥ p.1.1 = 2 := by
    rw [hpeq]
    exact h
  refine ⟨w, hw, p, hp, hp2, ?_⟩
  rw [hconj]
  exact refl_congr (congrArg Prod.fst hpeq).symm (congrArg Prod.snd hpeq).symm h hp2

theorem linTest_bframe_of_certOK {ℓ : ℕ} (S : Fin ℓ → (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1)))
    (gens : List (Vn (r + 1) × Vn (r + 1))) (hlen : gens.length = ℓ)
    (hS : ∀ k : Fin ℓ, S k = letLin (letAt gens k))
    {L : List ((Vn (r + 1) × Vn (r + 1)) × List ℕ × ℕ)} (hL : reflCertB gens L = true)
    (hF : bFrameB r L = true) {sets : List (List (Vn (r + 1)))}
    {pats : List ((Vn (r + 1) × Vn (r + 1)) × PatV (r + 1))} {reps : List (Vn (r + 1) × Vn (r + 1))}
    {s2 : List (S2V (r + 1))} (hOK : certOK gens (xLast r) sets pats reps s2 = true)
    (hcov : bCovB r pats = true) :
    ∀ A Mg : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1)),
      TestHyp (Subgroup.closure (Set.range S)) (xLast r) A Mg →
      ∀ t₁ ∈ Mg, IsRefl t₁ → ¬ FixesLine (xLast r) t₁ →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine (xLast r) t → t ∈ Mg := by
  intro A Mg hT r' hr hrR hrx t ht htR htx
  have hgens : AlphOK gens := by
    unfold certOK at hOK
    simp only [Bool.and_eq_true] at hOK
    exact AlphOK.of_all hOK.1.1.1.1
  have hgW : ∀ l ∈ gens, letLin l ∈ Subgroup.closure (Set.range S) := by
    intro l hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
    have hl' : letAt gens k = gens[k] := List.getD_eq_getElem _ _ hk
    rw [← hl', ← hS ⟨k, hlen ▸ hk⟩]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  have hWgen : Subgroup.closure (Set.range S) ≤
      Subgroup.closure {g | ∃ l ∈ gens, g = letLin l} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    refine Subgroup.subset_closure ⟨letAt gens k, ?_, hS k⟩
    have hk : k.val < gens.length := hlen ▸ k.isLt
    rw [show letAt gens k = gens[k.val] from List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  unfold bFrameB at hF
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hF
  obtain ⟨hDS, hFl⟩ := hF
  have hW : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff i j h ∈ Subgroup.closure (Set.range S) :=
    fun i j h => sgnDiff_eq_letLin i j h ▸ mem_of_reflCertB hgens hgW hL (hDS i j h).1
  have hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum i j h ∈ Subgroup.closure (Set.range S) :=
    fun i j h => sgnSum_eq_letLin i j h ▸ mem_of_reflCertB hgens hgW hL (hDS i j h).2
  have hWf : ∀ i : Fin r, sgnFlip i ∈ Subgroup.closure (Set.range S) :=
    fun i => sgnFlip_eq_letLin i ▸ mem_of_reflCertB hgens hgW hL (hFl i)
  exact hT.mem_of_certOK hOK hgW hWgen (hT.bframe_cover hW hWs hWf hcov) hr hrR hrx ht htR htx

@[expose] def dFrameB (r : ℕ) (L : List ((Vn (r + 1) × Vn (r + 1)) × List ℕ × ℕ)) : Bool :=
  decide (∀ i j : Fin r, i ≠ j → sgnDiffL i j ∈ L.map Prod.fst ∧ sgnSumL i j ∈ L.map Prod.fst)

@[expose] def dCovB (r : ℕ) (pats : List ((Vn (r + 1) × Vn (r + 1)) × PatV (r + 1))) : Bool :=
  bCovB r pats && [0, 1, 2].all fun l => [0, 1, 2].all fun g => [0, 1, 2].all fun d =>
    !(decide (canonAD r l d ⬝ᵥ canonD r g = 2) && movesB (xLast r) (canonD r g) (canonAD r l d))
      || decide ((canonD r g, canonAD r l d) ∈ pats.map Prod.fst)

theorem TestHyp.dframe_cover (hr : 3 ≤ r) (hT : TestHyp W (xLast r) A M)
    (hW : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum i j h ∈ W)
    {pats : List ((Vn (r + 1) × Vn (r + 1)) × PatV (r + 1))} (hcov : dCovB r pats = true) :
    ∀ u ∈ A, IsRefl u → ¬ FixesLine (xLast r) u → ∃ w ∈ W, ∃ p ∈ pats,
      ∃ h : p.1.2 ⬝ᵥ p.1.1 = 2, w * u * w⁻¹ = refl p.1.1 p.1.2 h := by
  intro u hu huR hux
  unfold dCovB at hcov
  rw [Bool.and_eq_true] at hcov
  obtain ⟨hcovB, hcovD⟩ := hcov
  obtain ⟨w, hw, k, -, hkr, hwx, hcase⟩ := hT.exists_canonical_D hr hW hWs hu huR hux
  have key : ∀ (c a : Vn (r + 1)) (h : a ⬝ᵥ c = 2), w * u * w⁻¹ = refl c a h →
      (c, a) ∈ pats.map Prod.fst → ∃ p ∈ pats, ∃ h : p.1.2 ⬝ᵥ p.1.1 = 2,
        w * u * w⁻¹ = refl p.1.1 p.1.2 h := by
    intro c a h hconj hc
    obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hc
    have hp2 : p.1.2 ⬝ᵥ p.1.1 = 2 := by
      rw [hpeq]
      exact h
    refine ⟨p, hp, hp2, ?_⟩
    rw [hconj]
    exact refl_congr (congrArg Prod.fst hpeq).symm (congrArg Prod.snd hpeq).symm h hp2
  refine ⟨w, hw, ?_⟩
  rcases hcase with ⟨l, g, d, h, hconj⟩ | ⟨-, l, g, d, h, hconj⟩
  · have hmv := movesB_of_conj hwx hux h hconj
    have hc := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
      hcovB k (List.mem_range.mpr (by omega))) l (zmod3_mem_list l)) g (zmod3_mem_list g)) d
      (zmod3_mem_list d)
    rw [show decide (canonA r k l d ⬝ᵥ canonC r k g = 2) = true from decide_eq_true h, hmv,
      Bool.and_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
    exact key _ _ h hconj hc
  · have hmv := movesB_of_conj hwx hux h hconj
    have hc := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hcovD l
      (zmod3_mem_list l)) g (zmod3_mem_list g)) d (zmod3_mem_list d)
    rw [show decide (canonAD r l d ⬝ᵥ canonD r g = 2) = true from decide_eq_true h, hmv,
      Bool.and_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
    exact key _ _ h hconj hc

theorem linTest_dframe_of_certOK (hr : 3 ≤ r) {ℓ : ℕ}
    (S : Fin ℓ → (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1)))
    (gens : List (Vn (r + 1) × Vn (r + 1))) (hlen : gens.length = ℓ)
    (hS : ∀ k : Fin ℓ, S k = letLin (letAt gens k))
    {L : List ((Vn (r + 1) × Vn (r + 1)) × List ℕ × ℕ)} (hL : reflCertB gens L = true)
    (hF : dFrameB r L = true) {sets : List (List (Vn (r + 1)))}
    {pats : List ((Vn (r + 1) × Vn (r + 1)) × PatV (r + 1))} {reps : List (Vn (r + 1) × Vn (r + 1))}
    {s2 : List (S2V (r + 1))} (hOK : certOK gens (xLast r) sets pats reps s2 = true)
    (hcov : dCovB r pats = true) :
    ∀ A Mg : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1)),
      TestHyp (Subgroup.closure (Set.range S)) (xLast r) A Mg →
      ∀ t₁ ∈ Mg, IsRefl t₁ → ¬ FixesLine (xLast r) t₁ →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine (xLast r) t → t ∈ Mg := by
  intro A Mg hT r' hr' hrR hrx t ht htR htx
  have hgens : AlphOK gens := by
    unfold certOK at hOK
    simp only [Bool.and_eq_true] at hOK
    exact AlphOK.of_all hOK.1.1.1.1
  have hgW : ∀ l ∈ gens, letLin l ∈ Subgroup.closure (Set.range S) := by
    intro l hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
    have hl' : letAt gens k = gens[k] := List.getD_eq_getElem _ _ hk
    rw [← hl', ← hS ⟨k, hlen ▸ hk⟩]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  have hWgen : Subgroup.closure (Set.range S) ≤
      Subgroup.closure {g | ∃ l ∈ gens, g = letLin l} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    refine Subgroup.subset_closure ⟨letAt gens k, ?_, hS k⟩
    have hk : k.val < gens.length := hlen ▸ k.isLt
    rw [show letAt gens k = gens[k.val] from List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  unfold dFrameB at hF
  rw [decide_eq_true_eq] at hF
  have hW : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff i j h ∈ Subgroup.closure (Set.range S) :=
    fun i j h => sgnDiff_eq_letLin i j h ▸ mem_of_reflCertB hgens hgW hL (hF i j h).1
  have hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum i j h ∈ Subgroup.closure (Set.range S) :=
    fun i j h => sgnSum_eq_letLin i j h ▸ mem_of_reflCertB hgens hgW hL (hF i j h).2
  exact hT.mem_of_certOK hOK hgW hWgen (hT.dframe_cover hr hW hWs hcov) hr' hrR hrx ht htR htx

end CFSG.StandardType.TestLin

end
