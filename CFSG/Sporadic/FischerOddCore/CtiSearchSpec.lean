module

public import CFSG.Sporadic.FischerOddCore.ClosureSearchSpec
public import CFSG.Sporadic.FischerOddCore.Fi22CTICheckInputs

public section

namespace CFSG.Sporadic.FischerOddCore.SearchSpec

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore
open CFSG.Sporadic.FischerOddCore.Native

@[expose] def ctStep (zi : Array ℕ) (i : ℕ) (s : Array ℕ × Array Bool × Array ℕ) :
    Id (ForInStep (Array ℕ × Array Bool × Array ℕ)) :=
  if (!s.2.1[i]!) = true then
    ForInStep.yield ((s.1.set! i s.2.2.size).set! zi[i]! s.2.2.size,
      (s.2.1.set! i true).set! zi[i]! true, s.2.2.push i)
  else ForInStep.yield (s.1, s.2.1, s.2.2)

theorem ctiCosets_eq_ct (E : Array (Array ℕ)) (z : Array ℕ) :
    ctiCosets E z =
      (have zi := E.map fun e => ((idxMap E E.size)[compA 3510 e z]?).getD E.size
      have s := forIn (m := Id) [:E.size]
        (Array.replicate E.size 0, Array.replicate E.size false, (#[] : Array ℕ)) (ctStep zi)
      (s.1, s.2.2, zi)) := rfl

theorem ctiPi_eq_idx (E : Array (Array ℕ)) (cid reps g gi : Array ℕ) :
    ctiPi E cid reps g gi =
      reps.map fun r => cid[((idxMap E E.size)[conjArr 3510 g gi E[r]!]?).getD 0]! := rfl

theorem strict_of_succ {R : ℕ} {f : ℕ → ℕ} (h : ∀ c, c + 1 < R → f c < f (c + 1)) :
    ∀ a b, a < b → b < R → f a < f b := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a b with h1 | h1
    · exact lt_trans (ih h1 (by omega)) (h b hb)
    · have e : a = b := by omega
      rw [e]
      exact h b hb

theorem ctiCosets_eq {E : Array (Array ℕ)} {z : Array ℕ} {cid reps zi : Array ℕ} {M R : ℕ}
    (hEs : E.size = M) (hinj : ∀ i < M, ∀ j < M, E[i]! = E[j]! → i = j)
    (hzs : zi.size = M) (hz : ∀ i < M, zi[i]! < M ∧ E[zi[i]!]! = compA 3510 E[i]! z)
    (hzz : ∀ i < M, zi[zi[i]!]! = i ∧ zi[i]! ≠ i) (hcs : cid.size = M) (hrs : reps.size = R)
    (hrep : ∀ c < R, reps[c]! < M ∧ cid[reps[c]!]! = c ∧ reps[c]! < zi[reps[c]!]!)
    (hinc : ∀ c, c + 1 < R → reps[c]! < reps[c + 1]!)
    (hcid : ∀ i < M, cid[i]! < R ∧ (reps[cid[i]!]! = i ∨ reps[cid[i]!]! = zi[i]!))
    (hcz : ∀ i < M, cid[zi[i]!]! = cid[i]!) :
    ctiCosets E z = (cid, reps, zi) := by
  have hstr := strict_of_succ (f := fun c => reps[c]!) hinc
  obtain ⟨hi1, -⟩ := idxMap_spec (E := E) (m := E.size) (by rw [hEs]; exact hinj)
  have hzi : (E.map fun e => ((idxMap E E.size)[compA 3510 e z]?).getD E.size) = zi := by
    refine Array.ext (by rw [Array.size_map, hEs, hzs]) fun i h1 h2 => ?_
    have hi : i < M := by rw [← hEs]; simpa using h1
    simp only [Array.getElem_map]
    rw [← getElem!_pos E i (by rw [hEs]; exact hi), ← (hz i hi).2,
      hi1 _ (by rw [hEs]; exact (hz i hi).1), Option.getD_some, getElem!_pos zi i h2]
  rw [ctiCosets_eq_ct]
  simp only [hzi]
  have key := forIn_range_yield (fun q (s : Array ℕ × Array Bool × Array ℕ) =>
      s.1.size = M ∧ s.2.1.size = M ∧
      (∀ j < M, s.2.1[j]! = true ↔ (j < q ∨ zi[j]! < q)) ∧
      (∀ j < M, s.2.1[j]! = true → s.1[j]! = cid[j]!) ∧
      ∃ m ≤ R, s.2.2.size = m ∧ (∀ c < m, s.2.2[c]! = reps[c]!) ∧
        ∀ c < R, (c < m ↔ reps[c]! < q))
    (ctStep zi) E.size (Array.replicate E.size 0, Array.replicate E.size false, #[])
    (fun q s hq hI => ?_) ?_
  · obtain ⟨hs1, hs2, hseen, hcd, m, hmR, hm, hrp, hmq⟩ := key
    rw [hEs] at hmq
    have hmR' : m = R := by
      refine le_antisymm hmR ?_
      rcases Nat.eq_zero_or_pos R with e | e
      · omega
      · have := (hmq (R - 1) (by omega)).2 (hrep (R - 1) (by omega)).1
        omega
    subst hmR'
    have e1 : (forIn (m := Id) [:E.size] (Array.replicate E.size 0, Array.replicate E.size false,
        (#[] : Array ℕ)) (ctStep zi)).1 = cid := by
      refine Array.ext (by rw [hs1, hcs]) fun j h1 h2 => ?_
      have hj : j < M := by rw [← hs1]; exact h1
      have := hcd j hj ((hseen j hj).2 (Or.inl (by rw [hEs]; exact hj)))
      rwa [getElem!_pos _ j h1, getElem!_pos _ j h2] at this
    have e2 : (forIn (m := Id) [:E.size] (Array.replicate E.size 0, Array.replicate E.size false,
        (#[] : Array ℕ)) (ctStep zi)).2.2 = reps := by
      refine Array.ext (by rw [hm, hrs]) fun c h1 h2 => ?_
      have := hrp c (by rw [← hm]; exact h1)
      rwa [getElem!_pos _ c h1, getElem!_pos _ c h2] at this
    rw [e1, e2]
  · obtain ⟨cd, sn, rp⟩ := s
    obtain ⟨hs1, hs2, hseen, hcd, m, hmR, hm, hrp, hmq⟩ := hI
    dsimp only at hs1 hs2 hseen hcd hm hrp
    have hqM : q < M := by rw [← hEs]; exact hq
    obtain ⟨hzq, -⟩ := hz q hqM
    obtain ⟨hzzq, hzne⟩ := hzz q hqM
    cases hsq : sn[q]! with
    | true =>
      refine ⟨(cd, sn, rp), by unfold ctStep; rw [hsq]; rfl, hs1, hs2, fun j hj => ?_,
        hcd, m, hmR, hm, hrp, fun c hc => ?_⟩
      · have hzq' : zi[q]! < q := by
          rcases (hseen q hqM).1 hsq with h | h
          · omega
          · exact h
        rw [hseen j hj]
        constructor
        · rintro (h | h)
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        · rintro (h | h)
          · rcases Nat.lt_or_ge j q with h1 | h1
            · exact Or.inl h1
            · have e : j = q := by omega
              rw [e]
              exact Or.inr hzq'
          · rcases Nat.lt_or_ge zi[j]! q with h1 | h1
            · exact Or.inr h1
            · have e : zi[j]! = q := by omega
              left
              have := (hzz j hj).1
              rw [e] at this
              omega
      · rw [hmq c hc]
        obtain ⟨hr1, -, hr3⟩ := hrep c hc
        constructor
        · intro h
          omega
        · intro h
          rcases Nat.lt_or_ge reps[c]! q with h1 | h1
          · exact h1
          · have e : reps[c]! = q := by omega
            have hzq' : zi[q]! < q := by
              rcases (hseen q hqM).1 hsq with h | h
              · omega
              · exact h
            rw [e] at hr3
            omega
    | false =>
      have hnot : ¬ zi[q]! < q := fun h => by
        have := (hseen q hqM).2 (Or.inr h)
        rw [hsq] at this
        exact Bool.noConfusion this
      have hgt : q < zi[q]! := by omega
      obtain ⟨hc0R, hc0⟩ := hcid q hqM
      have hrq : reps[cid[q]!]! = q := by
        rcases hc0 with h | h
        · exact h
        · exfalso
          have h3 := (hrep _ hc0R).2.2
          rw [h, hzzq] at h3
          omega
      have hmc : m = cid[q]! := by
        refine le_antisymm ?_ ?_
        · by_contra hlt
          have h4 := (hmq (cid[q]!) hc0R).1 (by omega)
          rw [hrq] at h4
          omega
        · by_contra hlt
          have h5 : reps[m]! < reps[cid[q]!]! := hstr _ _ (by omega) hc0R
          rw [hrq] at h5
          have h6 := (hmq m (by omega)).2 h5
          omega
      refine ⟨((cd.set! q rp.size).set! zi[q]! rp.size, (sn.set! q true).set! zi[q]! true,
        rp.push q), by unfold ctStep; rw [hsq]; rfl, ?_⟩
      dsimp only
      refine ⟨by rw [size_set!', size_set!', hs1], by rw [size_set!', size_set!', hs2],
        fun j hj => ?_, fun j hj hsj => ?_, m + 1, ?_, by rw [Array.size_push, hm], fun c hc => ?_,
        fun c hc => ?_⟩
      · rw [get!_set!_eq _ _ _ _ (by rw [size_set!', hs2]; exact hj),
          get!_set!_eq _ _ _ _ (by rw [hs2]; exact hj)]
        constructor
        · intro h
          split_ifs at h with h1 h2
          · right
            rw [← h1, hzzq]
            omega
          · left
            omega
          · rcases (hseen j hj).1 h with h3 | h3
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
        · intro h
          split_ifs with h1 h2
          · rfl
          · rfl
          · refine (hseen j hj).2 ?_
            rcases h with h3 | h3
            · rcases Nat.lt_or_ge j q with h4 | h4
              · exact Or.inl h4
              · exact absurd (by omega : q = j) h2
            · rcases Nat.lt_or_ge zi[j]! q with h4 | h4
              · exact Or.inr h4
              · exfalso
                have e : zi[j]! = q := by omega
                have := (hzz j hj).1
                rw [e] at this
                exact h1 this
      · rw [get!_set!_eq _ _ _ _ (by rw [size_set!', hs1]; exact hj),
          get!_set!_eq _ _ _ _ (by rw [hs1]; exact hj)]
        rw [get!_set!_eq _ _ _ _ (by rw [size_set!', hs2]; exact hj),
          get!_set!_eq _ _ _ _ (by rw [hs2]; exact hj)] at hsj
        split_ifs at hsj ⊢ with h1 h2
        · rw [hm, hmc, ← h1, hcz q hqM]
        · rw [hm, hmc, ← h2]
        · exact hcd j hj hsj
      · omega
      · rcases Nat.lt_or_ge c m with h1 | h1
        · rw [get!_push_lt _ _ (by rw [hm]; exact h1)]
          exact hrp c h1
        · have e : c = m := by omega
          rw [e, ← hm, get!_push_eq, hm, hmc, hrq]
      · constructor
        · intro h
          rcases Nat.lt_or_ge c m with h1 | h1
          · have := (hmq c hc).1 h1
            omega
          · have e : c = m := by omega
            rw [e, hmc, hrq]
            omega
        · intro h
          rcases Nat.lt_or_ge reps[c]! q with h1 | h1
          · have := (hmq c hc).2 h1
            omega
          · have e : reps[c]! = q := by omega
            have e2 : c = cid[q]! := by
              by_contra hne
              rcases Nat.lt_or_ge c (cid[q]!) with h2 | h2
              · have h3 : reps[c]! < reps[cid[q]!]! := hstr _ _ h2 hc0R
                rw [hrq] at h3
                omega
              · have h3 : reps[cid[q]!]! < reps[c]! := hstr _ _ (by omega) hc
                rw [hrq] at h3
                omega
            omega
  · refine ⟨by simp [hEs], by simp [hEs], fun j hj => ?_, fun j hj h => ?_, 0, Nat.zero_le _,
      rfl, fun c hc => absurd hc (Nat.not_lt_zero _), fun c hc => ?_⟩
    · have : (Array.replicate E.size false)[j]! = false := by
        rw [getElem!_pos _ j (by simp [hEs]; exact hj), Array.getElem_replicate]
      dsimp only
      rw [this]
      simp
    · have : (Array.replicate E.size false)[j]! = false := by
        rw [getElem!_pos _ j (by simp [hEs]; exact hj), Array.getElem_replicate]
      dsimp only at h
      rw [this] at h
      exact absurd h Bool.false_ne_true
    · simp

theorem ctiPi_eq {E : Array (Array ℕ)} {cid reps g gi π : Array ℕ}
    (hinj : ∀ i < E.size, ∀ j < E.size, E[i]! = E[j]! → i = j) (hπ : π.size = reps.size)
    (h : ∀ c < reps.size, ∃ j < E.size, E[j]! = conjArr 3510 g gi E[reps[c]!]! ∧
      cid[j]! = π[c]!) :
    ctiPi E cid reps g gi = π := by
  obtain ⟨hi1, -⟩ := idxMap_spec (E := E) (m := E.size) hinj
  rw [ctiPi_eq_idx]
  refine Array.ext (by rw [Array.size_map, hπ]) fun c h1 h2 => ?_
  have hc : c < reps.size := by simpa using h1
  obtain ⟨j, hj, hje, hjc⟩ := h c hc
  simp only [Array.getElem_map]
  rw [← getElem!_pos reps c hc, ← hje, hi1 j hj, Option.getD_some, hjc,
    getElem!_pos π c h2]

end CFSG.Sporadic.FischerOddCore.SearchSpec

end
