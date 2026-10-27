module

public import CFSG.Certificates.CosetTableOrders
public import CFSG.Certificates.CosetTableCompact

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

@[expose] def orderCheckF (ws : List (List (Fin m × Bool))) (S : List ℕ) (cap n : ℕ)
    (words : List (List (Fin m × Bool) × ℕ)) (fuel : ℕ) : Bool :=
  let P := colParams ws ((subsetOf m S).map fun x => [(x, true)])
  let st := enumerate P cap
  (!st.overflow && st.complete P.L && st.liveCount == n) &&
    invConsistentNative P.L (colInv ws) st && relsClosedNative P.L st (colCodes ws ws) &&
    words.all fun p => cycleLength P.L st.tab (p.1.map (colCode ws)) 1 fuel == p.2

theorem subsetCheckC_of_orderCheckF {ws : List (List (Fin m × Bool))} {S : List ℕ}
    {cap n : ℕ} {words : List (List (Fin m × Bool) × ℕ)} {fuel : ℕ}
    (h : orderCheckF ws S cap n words fuel = true) : subsetCheckC ws S cap n = true := by
  unfold orderCheckF at h
  unfold subsetCheckC check
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := h
  exact h1

theorem index_le_of_orderCheckF (ws : List (List (Fin m × Bool))) (S : List ℕ) {cap n : ℕ}
    {words : List (List (Fin m × Bool) × ℕ)} {fuel : ℕ}
    (h : orderCheckF ws S cap n words fuel = true) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).index ≤ n :=
  index_le_of_check (goodColParams ws _ _ (genSub_words_mem ws (subsetOf m S)))
    (by simpa [colParams, mkParams] using closure_colLetter ws)
    (subsetCheckC_of_orderCheckF h)

theorem dvd_orderOf_of_orderCheckF {ws : List (List (Fin m × Bool))} {S : List ℕ} {cap n : ℕ}
    {words : List (List (Fin m × Bool) × ℕ)} {fuel : ℕ}
    (h : orderCheckF ws S cap n words fuel = true) {u : List (Fin m × Bool)} {ℓ : ℕ}
    (hmem : (u, ℓ) ∈ words) (hℓ : 0 < ℓ) :
    ℓ ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u)) := by
  unfold orderCheckF at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hc⟩, -⟩, hi⟩, hrel⟩, hwords⟩ := h
  exact dvd_orderOf_of_walk hc hi hrel hℓ (hwords _ hmem)

@[expose] def orderCheckFC (ws : List (List (Fin m × Bool))) (S : List ℕ) (cap n : ℕ)
    (words : List (List (Fin m × Bool) × ℕ)) (fuel : ℕ) : Bool :=
  decide ((cap + 2) * ((cols ws).length + 1) ≤ 2 ^ 32) &&
    (let P := colParams ws ((subsetOf m S).map fun x => [(x, true)])
     let sc := enumerateC P cap
     (!sc.overflow && sc.completeC P.L && sc.liveCountC == n) &&
       (let st := sc.toSt
        invConsistentNative P.L (colInv ws) st && relsClosedNative P.L st (colCodes ws ws) &&
          words.all fun p => cycleLength P.L st.tab (p.1.map (colCode ws)) 1 fuel == p.2))

theorem orderCheckF_of_orderCheckFC {ws : List (List (Fin m × Bool))} {S : List ℕ} {cap n : ℕ}
    {words : List (List (Fin m × Bool) × ℕ)} {fuel : ℕ}
    (h : orderCheckFC ws S cap n words fuel = true) :
    orderCheckF ws S cap n words fuel = true := by
  unfold orderCheckFC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcap, hchk, hrest⟩ := h
  set P := colParams ws ((subsetOf m S).map fun x => [(x, true)]) with hP
  have hcap' : (cap + 2) * (P.L + 1) ≤ 2 ^ 32 := hcap
  have hcheck : checkC P cap n = true := by
    unfold checkC
    simpa using hchk
  rw [checkC_eq n hcap'] at hcheck
  unfold orderCheckF
  simp only [Bool.and_eq_true] at hrest ⊢
  rw [← enumerateC_toSt hcap']
  obtain ⟨⟨h1, h2⟩, h3⟩ := hrest
  refine ⟨⟨⟨?_, h1⟩, h2⟩, h3⟩
  rw [enumerateC_toSt hcap']
  unfold check at hcheck
  simp only [Bool.and_eq_true] at hcheck
  exact hcheck

theorem index_le_of_orderCheckFC (ws : List (List (Fin m × Bool))) (S : List ℕ) {cap n : ℕ}
    {words : List (List (Fin m × Bool) × ℕ)} {fuel : ℕ}
    (h : orderCheckFC ws S cap n words fuel = true) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).index ≤ n :=
  index_le_of_orderCheckF ws S (orderCheckF_of_orderCheckFC h)

end CFSG.CosetTable
