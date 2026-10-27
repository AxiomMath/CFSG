module

public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.UnitaryThreeRecognition.AbelianQFive

abbrev M := ZMod 5 × ZMod 5 × ZMod 5

@[expose] def gen (ν α β : ZMod 5) (u : M) : M := (ν * u.1, β * u.2.2, u.2.1 + α * u.2.2)

structure ValidTau (ν α β : ZMod 5) (m : ℕ) (τ : M → M) : Prop where
  zero : τ 0 = 0
  ne_zero : ∀ u, u ≠ 0 → τ u ≠ 0
  invol : ∀ u, u ≠ 0 → τ (τ u) = u
  equiv : ∀ u, u ≠ 0 → τ (gen ν α β u) = (gen ν α β)^[m] (τ u)
  center : ∀ u : M, u ≠ 0 → u.2 = 0 → (τ u).2 = 0
  moufang : ∀ u, u ≠ 0 → ∃ k : ℕ, ∀ w, w ≠ 0 → u + τ w ≠ 0 → w - τ (-u) ≠ 0 →
    τ (u + τ w) = τ u + (gen ν α β)^[k] (τ (w - τ (-u)))

@[expose] def allZ : List (ZMod 5) := [0, 1, 2, 3, 4]

@[expose] def allM : List M :=
  allZ.flatMap fun z => allZ.flatMap fun a => allZ.map fun b => (z, a, b)

@[expose] def code (u : M) : ℕ := 25 * u.1.val + 5 * u.2.1.val + u.2.2.val

structure Params where
  ν : ZMod 5
  α : ZMod 5
  β : ZMod 5
  m : ℕ

@[expose] def Params.g (P : Params) : M → M := gen P.ν P.α P.β

structure Tables where
  lookup : Array (Option (ℕ × ℕ))
  reps : Array M

@[expose] def orbitData (P : Params) : Tables :=
  let r := allM.foldl (init := ((Array.replicate 125 (none : Option (ℕ × ℕ))), (#[] : Array M)))
    fun (st : Array (Option (ℕ × ℕ)) × Array M) u =>
      if u = 0 then st
      else match st.1[code u]? with
        | some (some _) => st
        | _ =>
          let i := st.2.size
          let tab := (List.range 8).foldl (fun (tab : Array (Option (ℕ × ℕ))) k =>
            let v := P.g^[k] u
            match tab[code v]? with
            | some (some _) => tab
            | _ => tab.set! (code v) (some (i, k))) st.1
          (tab, st.2.push u)
  ⟨r.1, r.2⟩

@[expose] def look (D : Tables) (u : M) : Option (ℕ × ℕ) := (D.lookup[code u]?).join

@[expose] def tauA (P : Params) (D : Tables) (A : Array (Option M)) (u : M) : Option M :=
  if u = 0 then some 0
  else match look D u with
    | some (i, k) => (A[i]?.join).map fun v => P.g^[(P.m * k) % 8] v
    | none => none

@[expose] def chk (P : Params) (D : Tables) (A : Array (Option M)) : Bool :=
  (List.range D.reps.size).all (fun i =>
    match A[i]?.join, D.reps[i]? with
    | some v, some r =>
      decide (v ≠ 0) && (decide (r.2 = 0) == decide (v.2 = 0)) &&
        (match tauA P D A v with
          | some t => decide (t = r)
          | none => true)
    | _, _ => true) &&
  (List.range D.reps.size).all (fun i =>
    match D.reps[i]? with
    | none => true
    | some u =>
      match tauA P D A u, tauA P D A (-u) with
      | some tu, some tnu =>
        (List.range 8).any fun k => allM.all fun w =>
          decide (w = 0) ||
            match tauA P D A w with
            | none => true
            | some tw =>
              decide (u + tw = 0) || decide (w - tnu = 0) ||
                match tauA P D A (u + tw), tauA P D A (w - tnu) with
                | some t1, some t2 => decide (t1 = tu + P.g^[k] t2)
                | _, _ => true
      | _, _ => true)

@[expose] def extend (P : Params) (D : Tables) (A : Array (Option M)) (i : ℕ) (val : M) :
    Array (Option M) :=
  let A' := A.set! i (some val)
  match look D val with
  | some (j, k) =>
    if j ≠ i ∧ A'[j]? = some none then
      A'.set! j (some (P.g^[(8 - (P.m * k) % 8) % 8] (D.reps[i]?.getD 0)))
    else A'
  | none => A'

@[expose] def search (P : Params) (D : Tables) : ℕ → Array (Option M) → Bool
  | 0, _ => false
  | fuel + 1, A =>
    match A.findIdx? (· = none) with
    | none => !chk P D A
    | some i => allM.all fun val =>
        decide (val = 0) ||
          (let A'' := extend P D A i val
           !chk P D A'' || search P D fuel A'')

section Sound

variable {P : Params} {D : Tables} {τ : M → M}

theorem Params.g_def (P : Params) : P.g = gen P.ν P.α P.β := rfl

@[expose] def TablesOK (P : Params) (D : Tables) : Prop :=
  (∀ i (hi : i < D.reps.size), D.reps[i] ≠ 0) ∧
  ∀ u : M, u ≠ 0 → ∃ i k, look D u = some (i, k) ∧ ∃ hi : i < D.reps.size, P.g^[k] D.reps[i] = u

@[expose] def Agrees (D : Tables) (τ : M → M) (A : Array (Option M)) : Prop :=
  ∀ i (hi : i < D.reps.size) v, A[i]?.join = some v → τ D.reps[i] = v

theorem gen_zero (ν α β : ZMod 5) : gen ν α β 0 = 0 := by
  simp [gen]

theorem iterate_mod (h8 : ∀ u, P.g^[8] u = u) (n : ℕ) (u : M) : P.g^[n % 8] u = P.g^[n] u :=
  (show Function.IsPeriodicPt P.g 8 u from h8 u).iterate_mod_apply n

theorem g_injective (h8 : ∀ u, P.g^[8] u = u) : Function.Injective P.g := by
  refine Function.LeftInverse.injective (g := P.g^[7]) fun x => ?_
  rw [← Function.iterate_succ_apply P.g 7 x]
  exact h8 x

theorem iterate_ne_zero (h8 : ∀ u, P.g^[8] u = u) {u : M} (hu : u ≠ 0) (k : ℕ) :
    P.g^[k] u ≠ 0 := by
  intro h
  apply hu
  have h0 : P.g^[k] (0 : M) = 0 := Function.iterate_fixed (gen_zero P.ν P.α P.β) k
  exact (g_injective h8).iterate k (h.trans h0.symm)

theorem tau_iterate (hv : ValidTau P.ν P.α P.β P.m τ) (h8 : ∀ u, P.g^[8] u = u) {u : M}
    (hu : u ≠ 0) (k : ℕ) : τ (P.g^[k] u) = P.g^[P.m * k] (τ u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Params.g_def,
      hv.equiv _ (by rw [← Params.g_def]; exact iterate_ne_zero h8 hu k), ← Params.g_def, ih,
      ← Function.iterate_add_apply]
    congr 1
    rw [Nat.mul_succ]
    exact Nat.add_comm _ _

theorem tauA_eq (hT : TablesOK P D) (hv : ValidTau P.ν P.α P.β P.m τ)
    (h8 : ∀ u, P.g^[8] u = u) {A : Array (Option M)} (hA : Agrees D τ A) {u x : M}
    (h : tauA P D A u = some x) : x = τ u := by
  unfold tauA at h
  split_ifs at h with hu
  · cases h
    rw [hu, hv.zero]
  · obtain ⟨i, k, hl, hi, hik⟩ := hT.2 u hu
    rw [hl] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨v, hv', rfl⟩ := h
    rw [← hik, tau_iterate hv h8 (hT.1 i hi) k, hA i hi v hv', iterate_mod h8]

theorem chk_true (hT : TablesOK P D) (hv : ValidTau P.ν P.α P.β P.m τ)
    (h8 : ∀ u, P.g^[8] u = u) {A : Array (Option M)} (hA : Agrees D τ A) :
    chk P D A = true := by
  unfold chk
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · intro i hi
    rw [List.mem_range] at hi
    rw [Array.getElem?_eq_getElem hi]
    rcases hAi : A[i]?.join with _ | v
    · rfl
    · have hτ := hA i hi v hAi
      have hr0 := hT.1 i hi
      have hv0 : v ≠ 0 := hτ ▸ hv.ne_zero _ hr0
      have hc : (D.reps[i].2 = 0) ↔ (v.2 = 0) :=
        ⟨fun h => hτ ▸ hv.center _ hr0 h, fun h => by
          rw [← hv.invol _ hr0, hτ]; exact hv.center _ hv0 h⟩
      simp only [ne_eq, hv0, not_false_eq_true, decide_true, Bool.true_and, Bool.and_eq_true,
        beq_iff_eq, decide_eq_decide]
      refine ⟨hc, ?_⟩
      rcases ht : tauA P D A v with _ | t
      · rfl
      · simp only [decide_eq_true_eq]
        rw [tauA_eq hT hv h8 hA ht, ← hτ, hv.invol _ hr0]
  · intro i hi
    rw [List.mem_range] at hi
    rw [Array.getElem?_eq_getElem hi]
    simp only
    rcases htu : tauA P D A D.reps[i] with _ | tu
    · rfl
    rcases htn : tauA P D A (-D.reps[i]) with _ | tnu
    · rfl
    simp only
    have htu' := tauA_eq hT hv h8 hA htu
    have htn' := tauA_eq hT hv h8 hA htn
    obtain ⟨k₀, hk₀⟩ := hv.moufang _ (hT.1 i hi)
    rw [List.any_eq_true]
    refine ⟨k₀ % 8, List.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
    rw [List.all_eq_true]
    intro w _
    by_cases hw : w = 0
    · simp [hw]
    rcases htw : tauA P D A w with _ | tw
    · simp [hw]
    have htw' := tauA_eq hT hv h8 hA htw
    by_cases h1 : D.reps[i] + tw = 0
    · simp [h1]
    by_cases h2 : w - tnu = 0
    · simp [h2]
    rcases ht1 : tauA P D A (D.reps[i] + tw) with _ | t1
    · simp [hw, h1, h2, ht1]
    rcases ht2 : tauA P D A (w - tnu) with _ | t2
    · simp [hw, h1, h2, ht1]
    have ht1' := tauA_eq hT hv h8 hA ht1
    have ht2' := tauA_eq hT hv h8 hA ht2
    simp only [hw, h1, h2, ht1, decide_false, Bool.false_or, decide_eq_true_eq]
    rw [ht1', ht2', htu', iterate_mod h8, htw', htn', Params.g_def]
    rw [htw'] at h1
    rw [htn'] at h2
    exact hk₀ w hw h1 h2

theorem extend_size (P : Params) (D : Tables) (A : Array (Option M)) (i : ℕ) (val : M) :
    (extend P D A i val).size = A.size := by
  unfold extend
  rcases look D val with _ | ⟨j, k⟩
  · simp
  · simp only
    split_ifs <;> simp

theorem extend_agrees (hT : TablesOK P D) (hv : ValidTau P.ν P.α P.β P.m τ)
    (h8 : ∀ u, P.g^[8] u = u) {A : Array (Option M)} (hA : Agrees D τ A) {i : ℕ}
    (hi : i < D.reps.size) : Agrees D τ (extend P D A i (τ D.reps[i])) := by
  have hr0 := hT.1 i hi
  have hA' : Agrees D τ (A.set! i (some (τ D.reps[i]))) := by
    intro i' hi' v hv'
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hv'
    split_ifs at hv' with h1 h2
    · subst h1
      simp only [Option.join_some, Option.some.injEq] at hv'
      exact hv'
    · simp at hv'
    · exact hA i' hi' v hv'
  unfold extend
  rcases hl : look D (τ D.reps[i]) with _ | ⟨j, k⟩
  · exact hA'
  · simp only
    split_ifs with hj
    · intro i' hi' v hv'
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hv'
      split_ifs at hv' with h1 h2
      · subst h1
        simp only [Option.join_some, Option.some.injEq, Array.getElem?_eq_getElem hi,
          Option.getD_some] at hv'
        rw [← hv']
        obtain ⟨i₂, k₂, hl₂, hi₂, hik₂⟩ := hT.2 _ (hv.ne_zero _ hr0)
        have hjk : (j, k) = (i₂, k₂) := Option.some.inj (hl.symm.trans hl₂)
        obtain ⟨hj', hk'⟩ := Prod.mk.inj hjk
        subst hj' hk'
        have h1 : τ (τ D.reps[i]) = D.reps[i] := hv.invol _ hr0
        rw [← hik₂, tau_iterate hv h8 (hT.1 _ hi₂)] at h1
        rw [← h1, ← Function.iterate_add_apply, ← iterate_mod h8]
        have : ((8 - P.m * k % 8) % 8 + P.m * k) % 8 = 0 := by omega
        rw [this, Function.iterate_zero, id]
      · simp at hv'
      · exact hA' i' hi' v hv'
    · exact hA'

theorem mem_allZ (z : ZMod 5) : z ∈ allZ := by
  revert z
  decide

theorem mem_allM (u : M) : u ∈ allM := by
  obtain ⟨z, a, b⟩ := u
  unfold allM
  rw [List.mem_flatMap]
  refine ⟨z, mem_allZ _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨a, mem_allZ _, ?_⟩
  rw [List.mem_map]
  exact ⟨b, mem_allZ _, rfl⟩

theorem search_sound (hT : TablesOK P D) (hv : ValidTau P.ν P.α P.β P.m τ)
    (h8 : ∀ u, P.g^[8] u = u) :
    ∀ (fuel : ℕ) (A : Array (Option M)), A.size = D.reps.size → Agrees D τ A →
      search P D fuel A = true → False
  | 0, A, _, _, h => by simp [search] at h
  | fuel + 1, A, hs, hA, h => by
    unfold search at h
    rcases hf : A.findIdx? (· = none) with _ | i
    · rw [hf] at h
      simp only [chk_true hT hv h8 hA, Bool.not_true, Bool.false_eq_true] at h
    · rw [hf] at h
      simp only [List.all_eq_true] at h
      have hi : i < A.size := (Array.findIdx?_eq_some_iff_getElem.mp hf).1
      have hi' : i < D.reps.size := hs ▸ hi
      have hval := h (τ D.reps[i]) (mem_allM _)
      have hne : τ D.reps[i] ≠ 0 := hv.ne_zero _ (hT.1 i hi')
      simp only [hne, decide_false, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true'] at hval
      have hA'' := extend_agrees hT hv h8 hA hi'
      rcases hval with hval | hval
      · rw [chk_true hT hv h8 hA''] at hval
        exact Bool.noConfusion hval
      · exact search_sound hT hv h8 fuel _ ((extend_size P D A i _).trans hs) hA'' hval

end Sound

@[expose] def tablesOKb (P : Params) (D : Tables) : Bool :=
  (List.range D.reps.size).all (fun i =>
    match D.reps[i]? with
    | some r => decide (r ≠ 0)
    | none => true) &&
  allM.all (fun u =>
    decide (u = 0) ||
      match look D u with
      | some (i, k) =>
        match D.reps[i]? with
        | some r => decide (P.g^[k] r = u)
        | none => false
      | none => false)

theorem tablesOK_of_tablesOKb {P : Params} {D : Tables} (h : tablesOKb P D = true) :
    TablesOK P D := by
  unfold tablesOKb at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi => ?_, fun u hu => ?_⟩
  · have := h1 i (List.mem_range.mpr hi)
    rw [Array.getElem?_eq_getElem hi] at this
    simpa using this
  · have := h2 u (mem_allM u)
    simp only [hu, decide_false, Bool.false_or] at this
    rcases hl : look D u with _ | ⟨i, k⟩
    · rw [hl] at this
      exact absurd this Bool.false_ne_true
    · rw [hl] at this
      simp only at this
      rcases hr : D.reps[i]? with _ | r
      · rw [hr] at this
        exact absurd this Bool.false_ne_true
      · rw [hr] at this
        simp only [decide_eq_true_eq] at this
        obtain ⟨hi, hri⟩ := Array.getElem?_eq_some_iff.mp hr
        exact ⟨i, k, rfl, hi, by rw [hri]; exact this⟩

@[expose] def g8b (P : Params) : Bool := allM.all fun u => decide (P.g^[8] u = u)

theorem g8_of_g8b {P : Params} (h : g8b P = true) (u : M) : P.g^[8] u = u := by
  unfold g8b at h
  rw [List.all_eq_true] at h
  simpa using h u (mem_allM u)

end CFSG.UnitaryThreeRecognition.AbelianQFive
