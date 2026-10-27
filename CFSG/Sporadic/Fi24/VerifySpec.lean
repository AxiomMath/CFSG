module

public import CFSG.Sporadic.Fi24.LoopSpec
public import Certificates.Data.CFSGNative.Fi24.Certificate

public section

namespace CFSG.Sporadic.Fi24.Native

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

structure EnumFacts (E : Enum) (n : ℕ) : Prop where
  alpha_size : E.alpha.size = n
  beta_size : E.beta.size = n
  par_size : E.par.size = n
  lab_size : E.lab.size = n
  L3 : 3 ≤ E.starts.size
  st0 : E.st 0 = 0
  st1 : E.st 1 = 1
  stL : E.st (E.starts.size - 1) = n
  lab0 : ap E.lab 0 = 0
  mono : ∀ m, m < E.starts.size - 1 → E.st m < E.st (m + 1)
  alpha_lt : ∀ k < n, ap E.alpha k < n
  beta_lt : ∀ k < n, ap E.beta k < n
  alpha_invo : ∀ k < n, ap E.alpha (ap E.alpha k) = k
  beta_ord3 : ∀ k < n, ap E.beta (ap E.beta (ap E.beta k)) = k
  tree : ∀ m, 1 ≤ m → m < E.starts.size - 1 → ∀ k, E.st m ≤ k → k < E.st (m + 1) →
    E.st (m - 1) ≤ ap E.par k ∧ ap E.par k < E.st m ∧
      ((ap E.lab k = 1 ∧ ap E.alpha (ap E.par k) = k) ∨
        (ap E.lab k = 2 ∧ ap E.beta (ap E.par k) = k))

theorem enumFacts_of {E : Enum} {n : ℕ} (h : enumOK E n = true) : EnumFacts E n := by
  unfold enumOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have := (allIn_eq_true.1 h10) m (Nat.zero_le _) hm
    simpa using this
  · intro k hk
    have := (allIn_eq_true.1 h11) k (Nat.zero_le _) hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · intro k hk
    have := (allIn_eq_true.1 h11) k (Nat.zero_le _) hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  · intro k hk
    have := (allIn_eq_true.1 h12) k (Nat.zero_le _) hk
    simpa using this
  · intro k hk
    have := (allIn_eq_true.1 h13) k (Nat.zero_le _) hk
    simpa using this
  · intro m hm1 hm k hk1 hk2
    have := (allIn_eq_true.1 ((allIn_eq_true.1 h14) m hm1 hm)) k hk1 hk2
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    exact ⟨h1, h2, h3⟩

section Levels

variable {E : Enum} {n : ℕ} (hE : EnumFacts E n)
include hE

theorem EnumFacts.st_mono {m m' : ℕ} (hmm : m ≤ m') (hm' : m' < E.starts.size) :
    E.st m ≤ E.st m' := by
  induction m' with
  | zero => rw [Nat.le_zero.1 hmm]
  | succ m' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hmm) with h | h
    · exact le_trans (ih (by omega) (by omega)) (le_of_lt (hE.mono m' (by omega)))
    · rw [h]

theorem EnumFacts.st_strict {m m' : ℕ} (hmm : m < m') (hm' : m' < E.starts.size) :
    E.st m < E.st m' :=
  lt_of_lt_of_le (hE.mono m (by omega)) (hE.st_mono (by omega) hm')

theorem EnumFacts.st_le_n {m : ℕ} (hm : m < E.starts.size) : E.st m ≤ n := by
  rw [← hE.stL]; exact hE.st_mono (by omega) (by omega)

theorem EnumFacts.exists_level {k : ℕ} (hk : k < n) :
    ∃ m, m < E.starts.size - 1 ∧ E.st m ≤ k ∧ k < E.st (m + 1) := by
  classical
  let m := Nat.findGreatest (fun m => E.st m ≤ k) (E.starts.size - 2)
  have h0 : E.st 0 ≤ k := by rw [hE.st0]; omega
  have hm : E.st m ≤ k := Nat.findGreatest_spec (P := fun m => E.st m ≤ k) (Nat.zero_le _) h0
  have hmle : m ≤ E.starts.size - 2 := Nat.findGreatest_le _
  refine ⟨m, by have := hE.L3; omega, hm, ?_⟩
  by_cases hlast : m + 1 ≤ E.starts.size - 2
  · have := Nat.findGreatest_is_greatest (P := fun m => E.st m ≤ k) (Nat.lt_succ_self m) hlast
    simp only [not_le] at this
    exact this
  · have : m + 1 = E.starts.size - 1 := by have := hE.L3; omega
    rw [this, hE.stL]; exact hk

theorem EnumFacts.level_unique {k m m' : ℕ} (hm : m < E.starts.size - 1)
    (hm' : m' < E.starts.size - 1) (h1 : E.st m ≤ k) (h2 : k < E.st (m + 1))
    (h1' : E.st m' ≤ k) (h2' : k < E.st (m' + 1)) : m = m' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hE.st_mono (show m + 1 ≤ m' by omega) (by omega); omega
  · have := hE.st_mono (show m' + 1 ≤ m by omega) (by omega); omega

theorem EnumFacts.par_lt {k : ℕ} (hk : k < n) (hk0 : 0 < k) : ap E.par k < k := by
  obtain ⟨m, hm, h1, h2⟩ := hE.exists_level hk
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    subst this
    rw [hE.st1] at h2; omega
  exact lt_of_lt_of_le (hE.tree m hm1 hm k h1 h2).2.1 h1

theorem EnumFacts.treeEdge {k : ℕ} (hk : k < n) (hk0 : 0 < k) :
    ap E.par k < k ∧ ((ap E.lab k = 1 ∧ ap E.alpha (ap E.par k) = k) ∨
      (ap E.lab k = 2 ∧ ap E.beta (ap E.par k) = k)) := by
  obtain ⟨m, hm, h1, h2⟩ := hE.exists_level hk
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    subst this
    rw [hE.st1] at h2; omega
  obtain ⟨-, h3, h4⟩ := hE.tree m hm1 hm k h1 h2
  exact ⟨lt_of_lt_of_le h3 h1, h4⟩

end Levels

theorem formAt_zero (gens : Unit → Gens) (E : Enum) (R0 : RRef) : formAt gens E R0 0 = R0 := by
  rw [formAt]; simp

theorem formAt_pos (gens : Unit → Gens) (E : Enum) (R0 : RRef) {k : ℕ} (hk0 : 0 < k)
    (hp : ap E.par k < k) :
    formAt gens E R0 k =
      stepForm ((gens ()).get (ap E.lab k)) (formAt gens E R0 (ap E.par k)).rows := by
  rw [formAt, dite_eq_left ⟨hk0, hp⟩]

@[expose] noncomputable def lvlForms (gens : Unit → Gens) (E : Enum) (R0 : RRef) (m : ℕ) :
    Array RRef :=
  (Array.range (E.st (m + 1) - E.st m)).map fun q => formAt gens E R0 (E.st m + q)

theorem lvlForms_size (gens : Unit → Gens) (E : Enum) (R0 : RRef) (m : ℕ) :
    (lvlForms gens E R0 m).size = E.st (m + 1) - E.st m := by
  unfold lvlForms; simp

theorem lvlForms_get (gens : Unit → Gens) (E : Enum) (R0 : RRef) {m k : ℕ} (h1 : E.st m ≤ k)
    (h2 : k < E.st (m + 1)) : (lvlForms gens E R0 m)[k - E.st m]! = formAt gens E R0 k := by
  unfold lvlForms
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_map, Array.getElem_range,
    Nat.add_sub_cancel' h1]

theorem nextLevel_eq (gens : Unit → Gens) {E : Enum} {n : ℕ} (hE : EnumFacts E n) (R0 : RRef)
    (chunks : ℕ) {m : ℕ} (hm : m + 2 < E.starts.size) :
    nextLevel gens E chunks m (lvlForms gens E R0 m) = lvlForms gens E R0 (m + 1) := by
  unfold nextLevel
  rw [parRange_eq]
  conv_rhs => unfold lvlForms
  apply Array.ext'
  simp only [Array.toList_map, Array.toList_range]
  apply List.map_congr_left
  intro q hq
  rw [List.mem_range] at hq
  set k := E.st (m + 1) + q
  have hk1 : E.st (m + 1) ≤ k := by omega
  have hk2' : k < E.st (m + 2) := by omega
  have hk2 : k < E.st (m + 1 + 1) := hk2'
  obtain ⟨hp1, hp2, -⟩ := hE.tree (m + 1) (by omega) (by omega) k hk1 hk2
  have hk0 : 0 < k := by
    have := hE.st_mono (show 1 ≤ m + 1 by omega) (by omega); rw [hE.st1] at this; omega
  simp only [Nat.add_sub_cancel] at hp1
  rw [lvlForms_get gens E R0 hp1 hp2, ← formAt_pos gens E R0 hk0 (lt_of_lt_of_le hp2 hk1)]

@[expose] noncomputable def prevOf (gens : Unit → Gens) (E : Enum) (R0 : RRef) (m : ℕ) :
    Array RRef :=
  if m = 0 then #[] else lvlForms gens E R0 (m - 1)

@[expose] noncomputable def hashesFrom (gens : Unit → Gens) (E : Enum) (R0 : RRef) (m : ℕ) :
    Array UInt64 :=
  if m + 1 < E.starts.size then
    (lvlForms gens E R0 m).map (fun F => hashRows F.rows) ++ hashesFrom gens E R0 (m + 1)
  else #[]
termination_by E.starts.size - m

theorem verifyFrom_spec (gens : Unit → Gens) {E : Enum} {n : ℕ} (hE : EnumFacts E n) (R0 : RRef)
    (chunks : ℕ) : ∀ (fuel m : ℕ) (hs : Array UInt64), m + 1 < E.starts.size →
      (verifyFrom gens E chunks fuel m (prevOf gens E R0 m) (lvlForms gens E R0 m) hs).1 = true →
      (∀ m', m ≤ m' → m' + 1 < E.starts.size →
        checkLevel gens E chunks m' (prevOf gens E R0 m') (lvlForms gens E R0 m') = true) ∧
      (verifyFrom gens E chunks fuel m (prevOf gens E R0 m) (lvlForms gens E R0 m) hs).2 =
        hs ++ hashesFrom gens E R0 m := by
  intro fuel
  induction fuel with
  | zero => intro m hs _ h; simp [verifyFrom] at h
  | succ fuel ih =>
    intro m hs hm h
    rw [verifyFrom] at h ⊢
    by_cases hc : checkLevel gens E chunks m (prevOf gens E R0 m) (lvlForms gens E R0 m) = true
    · rw [ite_eq_left hc] at h ⊢
      by_cases hnext : m + 2 < E.starts.size
      · rw [ite_eq_left hnext] at h ⊢
        have hprev : lvlForms gens E R0 m = prevOf gens E R0 (m + 1) := by
          unfold prevOf; simp
        rw [nextLevel_eq gens hE R0 chunks hnext, hprev] at h ⊢
        obtain ⟨h1, h2⟩ := ih (m + 1) _ (by omega) h
        refine ⟨fun m' hm' hm'' => ?_, ?_⟩
        · rcases Nat.lt_or_ge m m' with hlt | hge
          · exact h1 m' hlt hm''
          · rw [show m' = m by omega]; exact hc
        · rw [h2, Array.append_assoc]
          congr 1
          conv_rhs => rw [hashesFrom, ite_eq_left hm]
          rw [← hprev]
      · rw [ite_eq_right hnext] at h ⊢
        refine ⟨fun m' hm' hm'' => ?_, ?_⟩
        · rw [show m' = m by omega]; exact hc
        · show hs ++ (lvlForms gens E R0 m).map (fun F => hashRows F.rows) = _
          congr 1
          rw [hashesFrom, ite_eq_left hm, hashesFrom, ite_eq_right (by omega), Array.append_empty]
    · rw [ite_eq_right hc] at h
      simp at h

theorem lookupForm_cur (gens : Unit → Gens) (E : Enum) (R0 : RRef) {m x : ℕ}
    (h1 : E.st m ≤ x) (h2 : x < E.st (m + 1)) :
    lookupForm E m (prevOf gens E R0 m) (lvlForms gens E R0 m) x = formAt gens E R0 x := by
  unfold lookupForm; rw [ite_eq_left h1, lvlForms_get gens E R0 h1 h2]

theorem lookupForm_prev (gens : Unit → Gens) (E : Enum) (R0 : RRef) {m x : ℕ} (hm : 0 < m)
    (h1 : E.st (m - 1) ≤ x) (h2 : x < E.st m) :
    lookupForm E m (prevOf gens E R0 m) (lvlForms gens E R0 m) x = formAt gens E R0 x := by
  unfold lookupForm prevOf
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have h2' : x < E.st (m - 1 + 1) := by rwa [Nat.sub_add_cancel hm]
  exact lvlForms_get gens E R0 h1 h2'

@[expose] def tabOf (E : Enum) (g : ℕ) : Table := if g = 1 then E.alpha else E.beta

@[expose] def RelEdge (E : Enum) (k g : ℕ) : Prop :=
  (g = 1 ∧ ap E.alpha k < k) ∨ (g = 2 ∧ ap E.beta k < k ∧ ap E.beta (ap E.beta k) < k)

section Edges

variable {E : Enum} {n : ℕ} (hE : EnumFacts E n) {R0 : RRef} {chunks : ℕ}
  (hcheck : ∀ m, m + 1 < E.starts.size →
    checkLevel gensT E chunks m (prevOf gensT E R0 m) (lvlForms gensT E R0 m) = true)
include hE hcheck

omit hE in
theorem checkAt {m k : ℕ} (hm : m + 1 < E.starts.size)
    (hk1 : (if m = 0 then E.st 0 else E.st (m - 1)) ≤ k) (hk2 : k < E.st (m + 1)) :
    (E.st m ≤ k → rrefOK 253 (formAt gensT E R0 k) = true) ∧
      edgeCheck (gensT ()) E m (prevOf gensT E R0 m) (lvlForms gensT E R0 m) k 1 = true ∧
      edgeCheck (gensT ()) E m (prevOf gensT E R0 m) (lvlForms gensT E R0 m) k 2 = true := by
  have h := parAllWith_spec (hcheck m hm) k hk1 hk2
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun hk => ?_, h2, h3⟩
  rw [ite_eq_left hk, lvlForms_get gensT E R0 hk hk2] at h1
  exact h1

theorem rrefOK_formAt {k : ℕ} (hk : k < n) : rrefOK 253 (formAt gensT E R0 k) = true := by
  obtain ⟨m, hm, h1, h2⟩ := hE.exists_level hk
  refine (checkAt hcheck (m := m) (by omega) ?_ h2).1 h1
  split_ifs
  · rw [hE.st0]; omega
  · exact le_trans (hE.st_mono (by omega) (by omega)) h1

end Edges

theorem inLevel_iff (E : Enum) (m x : ℕ) :
    E.inLevel m x = true ↔ E.st m ≤ x ∧ x < E.st (m + 1) := by
  unfold Enum.inLevel; simp

theorem edgeCompare_spec {gens : Unit → Gens} {E : Enum} {R0 : RRef} {m k g j : ℕ}
    (h : edgeCompare (gens ()) E m (prevOf gens E R0 m) (lvlForms gens E R0 m) k g j = true)
    (hk : lookupForm E m (prevOf gens E R0 m) (lvlForms gens E R0 m) k = formAt gens E R0 k)
    (hj : lookupForm E m (prevOf gens E R0 m) (lvlForms gens E R0 m) j = formAt gens E R0 j) :
    stepForm ((gens ()).get g) (formAt gens E R0 k).rows = formAt gens E R0 j := by
  unfold edgeCompare at h
  rw [hk, hj, beq_iff_eq] at h
  exact h

section Edges2

variable {E : Enum} {n : ℕ} (hE : EnumFacts E n) {R0 : RRef} {chunks : ℕ}
  (hcheck : ∀ m, m + 1 < E.starts.size →
    checkLevel gensT E chunks m (prevOf gensT E R0 m) (lvlForms gensT E R0 m) = true)
include hE hcheck

omit hcheck in
theorem tabOf_lt {k g : ℕ} (hk : k < n) : ap (tabOf E g) k < n := by
  unfold tabOf; split_ifs
  · exact hE.alpha_lt k hk
  · exact hE.beta_lt k hk

theorem edge_spec {k g : ℕ} (hk : k < n) (hg : g = 1 ∨ g = 2) :
    RelEdge E k g ∨
      stepForm ((gensT ()).get g) (formAt gensT E R0 k).rows =
        formAt gensT E R0 (ap (tabOf E g) k) := by
  have hj : ap (tabOf E g) k < n := tabOf_lt hE hk
  by_cases hskip : skipEdge E k g = true
  ·
    have htree : ∀ j, j = ap (tabOf E g) k → ap E.par j = k → ap E.lab j = g →
        stepForm ((gensT ()).get g) (formAt gensT E R0 k).rows = formAt gensT E R0 j := by
      intro j hjk hpar hlab
      have hj0 : 0 < j := by
        by_contra h0
        have : j = 0 := by omega
        subst this
        rw [hE.lab0] at hlab
        rcases hg with rfl | rfl <;> exact absurd hlab (by decide)
      rw [formAt_pos gensT E R0 hj0 (hE.par_lt (hjk ▸ hj) hj0), hpar, hlab]
    unfold skipEdge at hskip
    rcases hg with rfl | rfl
    · simp only [ite_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hskip
      rcases hskip with h | ⟨h1, h2⟩
      · exact Or.inl (Or.inl ⟨rfl, h⟩)
      · exact Or.inr (htree _ (by simp [tabOf]) h1 h2)
    · simp only [show (2 : ℕ) ≠ 1 by decide, ite_false, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq] at hskip
      rcases hskip with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Or.inr ⟨rfl, h1, h2⟩)
      · exact Or.inr (htree _ (by simp [tabOf]) h1 h2)
  · right
    obtain ⟨m, hm, h1, h2⟩ := hE.exists_level hk
    have hlo : (if m = 0 then E.st 0 else E.st (m - 1)) ≤ k := by
      split_ifs
      · rw [hE.st0]; omega
      · exact le_trans (hE.st_mono (by omega) (by omega)) h1
    have hc := checkAt hcheck (m := m) (by omega) hlo h2
    have hec :
        edgeCheck (gensT ()) E m (prevOf gensT E R0 m) (lvlForms gensT E R0 m) k g = true := by
      rcases hg with rfl | rfl
      · exact hc.2.1
      · exact hc.2.2
    unfold edgeCheck at hec
    rw [ite_eq_right hskip] at hec
    have hjdef : (if g = 1 then ap E.alpha k else ap E.beta k) = ap (tabOf E g) k := by
      unfold tabOf; split_ifs <;> rfl
    simp only [hjdef] at hec
    set j := ap (tabOf E g) k with hjset
    have hink : E.inLevel m k = true := (inLevel_iff E m k).2 ⟨h1, h2⟩
    rw [ite_eq_left hink] at hec
    by_cases hwin : (E.inLevel m j || (0 < m && E.inLevel (m - 1) j)) = true
    · rw [ite_eq_left hwin] at hec
      refine edgeCompare_spec hec (lookupForm_cur gensT E R0 h1 h2) ?_
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, inLevel_iff] at hwin
      rcases hwin with ⟨hj1, hj2⟩ | ⟨hm0, hj1, hj2⟩
      · exact lookupForm_cur gensT E R0 hj1 hj2
      · rw [Nat.sub_add_cancel hm0] at hj2
        exact lookupForm_prev gensT E R0 hm0 hj1 hj2
    · rw [ite_eq_right hwin] at hec
      rw [inLevel_iff] at hec
      obtain ⟨hj1, hj2⟩ := hec
      have hm2 : m + 2 < E.starts.size := by
        by_contra hge
        have : E.st (m + 1) = n := by
          rw [show m + 1 = E.starts.size - 1 by omega]; exact hE.stL
        omega
      have hlo' : (if m + 1 = 0 then E.st 0 else E.st (m + 1 - 1)) ≤ k := by
        rw [ite_eq_right (by omega), Nat.add_sub_cancel]; exact h1
      have hc' := checkAt hcheck (m := m + 1) (by omega) hlo'
        (lt_of_lt_of_le h2 (le_of_lt (hE.mono (m + 1) (by omega))))
      have hec' : edgeCheck (gensT ()) E (m + 1) (prevOf gensT E R0 (m + 1))
          (lvlForms gensT E R0 (m + 1)) k g = true := by
        rcases hg with rfl | rfl
        · exact hc'.2.1
        · exact hc'.2.2
      unfold edgeCheck at hec'
      rw [ite_eq_right hskip] at hec'
      simp only [hjdef] at hec'
      have hnk : E.inLevel (m + 1) k = false := by
        rw [Bool.eq_false_iff]; intro h; rw [inLevel_iff] at h; omega
      have hinj : E.inLevel (m + 1) j = true := (inLevel_iff E (m + 1) j).2 ⟨hj1, hj2⟩
      rw [ite_eq_right (by rw [hnk]; decide), ite_eq_left hinj] at hec'
      refine edgeCompare_spec hec' ?_ (lookupForm_cur gensT E R0 hj1 hj2)
      exact lookupForm_prev gensT E R0 (by omega) (by rw [Nat.add_sub_cancel]; exact h1) h2

end Edges2

theorem hashesFrom_toList (gens : Unit → Gens) {E : Enum} {n : ℕ} (hE : EnumFacts E n)
    (R0 : RRef) : ∀ d m, m + d = E.starts.size - 1 →
      (hashesFrom gens E R0 m).toList =
        (List.range (n - E.st m)).map fun i => hashRows (formAt gens E R0 (E.st m + i)).rows := by
  intro d
  induction d with
  | zero =>
    intro m hm
    rw [hashesFrom, ite_eq_right (by omega), show m = E.starts.size - 1 by omega, hE.stL]
    simp
  | succ d ih =>
    intro m hm
    rw [hashesFrom, ite_eq_left (by omega), Array.toList_append, ih (m + 1) (by omega)]
    have hle : E.st m ≤ E.st (m + 1) := le_of_lt (hE.mono m (by omega))
    have hle2 : E.st (m + 1) ≤ n := hE.st_le_n (by omega)
    rw [show n - E.st m = (E.st (m + 1) - E.st m) + (n - E.st (m + 1)) by omega, List.range_add,
      List.map_append, List.map_map]
    unfold lvlForms
    simp only [Array.toList_map, Array.toList_range, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    congr 3
    omega

structure OrbitFacts (E : Enum) (R0 : RRef) (n : ℕ) : Prop where
  enum : EnumFacts E n
  rref : ∀ k < n, rrefOK 253 (formAt gensT E R0 k) = true
  edge : ∀ k < n, ∀ g, g = 1 ∨ g = 2 → RelEdge E k g ∨
    stepForm ((gensT ()).get g) (formAt gensT E R0 k).rows = formAt gensT E R0 (ap (tabOf E g) k)
  hash_inj : ∀ i < n, ∀ j < n,
    hashRows (formAt gensT E R0 i).rows = hashRows (formAt gensT E R0 j).rows → i = j

theorem orbitVerify_spec {E : Enum} {R0 : RRef} {n chunks : ℕ}
    (h : orbitVerify gensT E R0 n chunks = true) : OrbitFacts E R0 n := by
  unfold orbitVerify at h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
  have hE := enumFacts_of h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨⟨h3, h4⟩, h5⟩ := h2
  have hl0 : (#[R0] : Array RRef) = lvlForms gensT E R0 0 := by
    unfold lvlForms
    rw [hE.st0, hE.st1]
    apply Array.ext'
    simp [formAt_zero]
  have hp0 : (#[] : Array RRef) = prevOf gensT E R0 0 := by unfold prevOf; simp
  rw [hl0, hp0] at h3 h4 h5
  have hL : 0 + 1 < E.starts.size := by have := hE.L3; omega
  obtain ⟨hcheck, hhash⟩ := verifyFrom_spec gensT hE R0 chunks _ 0 #[] hL h3
  have hcheck' : ∀ m, m + 1 < E.starts.size →
      checkLevel gensT E chunks m (prevOf gensT E R0 m) (lvlForms gensT E R0 m) = true :=
    fun m hm => hcheck m (Nat.zero_le _) hm
  refine ⟨hE, fun k hk => rrefOK_formAt hE hcheck' hk,
    fun k hk g hg => edge_spec hE hcheck' hk hg, ?_⟩
  intro i hi j hj hij
  rw [hhash, Array.empty_append] at h5
  have hnd := distinctHashes_nodup h5
  rw [hashesFrom_toList gensT hE R0 (E.starts.size - 1) 0 (by omega), hE.st0, Nat.sub_zero] at hnd
  simp only [Nat.zero_add] at hnd
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 hi) (List.mem_range.2 hj) hij

end CFSG.Sporadic.Fi24.Native
