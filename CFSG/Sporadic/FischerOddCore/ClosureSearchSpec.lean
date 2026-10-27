module

public import CFSG.Sporadic.FischerOddCore.ClosureSpec

public section

namespace CFSG.Sporadic.FischerOddCore.SearchSpec

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore.Native

abbrev CSt : Type := Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap (Array ℕ) ℕ × ℕ

abbrev KSt : Type := Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap (Array ℕ) ℕ

@[expose] def csInner (n : ℕ) (gens : Array (Array ℕ)) (head : ℕ) (x : Array ℕ) (k : ℕ)
    (s : KSt) : Id (ForInStep KSt) :=
  if (!s.2.2.2.contains (compA n gens[k]! x)) = true then
    ForInStep.yield (s.1.push (compA n gens[k]! x), s.2.1.push head, s.2.2.1.push k,
      s.2.2.2.insert (compA n gens[k]! x) s.1.size)
  else ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2)

@[expose] def csOuter (n : ℕ) (gens : Array (Array ℕ)) (_ : ℕ) (s : CSt) : Id (ForInStep CSt) :=
  if s.2.2.2.2 < s.1.size then
    have r : KSt := forIn (m := Id) [:gens.size] (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
      (csInner n gens s.2.2.2.2 s.1[s.2.2.2.2]!)
    ForInStep.yield (r.1, r.2.1, r.2.2.1, r.2.2.2, s.2.2.2.2 + 1)
  else ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2)

@[expose] def csInit (n : ℕ) : CSt :=
  (#[idA n], #[0], #[0], ({} : Std.HashMap (Array ℕ) ℕ).insert (idA n) 0, 0)

@[expose] def csRow (n : ℕ) (gens E : Array (Array ℕ)) (idx : Std.HashMap (Array ℕ) ℕ) (i : ℕ)
    (k : ℕ) (a : Array ℕ) : Id (ForInStep (Array ℕ)) :=
  ForInStep.yield (a.set! (i * gens.size + k) (idx.getD (compA n gens[k]! E[i]!) E.size))

@[expose] def csNxt (n : ℕ) (gens E : Array (Array ℕ)) (idx : Std.HashMap (Array ℕ) ℕ) :
    Array ℕ :=
  forIn (m := Id) [:E.size] (Array.replicate (E.size * gens.size) E.size) fun i a =>
    ForInStep.yield (forIn (m := Id) [:gens.size] a (csRow n gens E idx i))

theorem closureSearch_eq_cs (n : ℕ) (gens : Array (Array ℕ)) (bound : ℕ) :
    closureSearch n gens bound =
      (have s : CSt := forIn (m := Id) [:bound] (csInit n) (csOuter n gens)
      (s.1, s.2.1, s.2.2.1, csNxt n gens s.1 s.2.2.2.1)) := rfl

theorem forIn_range'_break {β : Type} (I : ℕ → β → Prop) (Q : β → Prop)
    (f : ℕ → β → Id (ForInStep β)) : ∀ (m s : ℕ) (b : β),
    (∀ q b, s ≤ q → q < s + m → I q b →
      (∀ b', f q b = ForInStep.yield b' → I (q + 1) b') ∧
        (∀ b', f q b = ForInStep.done b' → Q b')) →
    (∀ b, I (s + m) b → Q b) → I s b → Q (forIn (m := Id) (List.range' s m) b f)
  | 0, s, b, _, hend, h0 => hend b (by simpa using h0)
  | m + 1, s, b, hstep, hend, h0 => by
    rw [List.range'_succ, List.forIn_cons]
    have hs := hstep s b (Nat.le_refl _) (by omega) h0
    cases hf : f s b with
    | done b' => exact hs.2 b' hf
    | yield b' =>
      have e : s + (m + 1) = s + 1 + m := by omega
      exact forIn_range'_break I Q f m (s + 1) b'
        (fun q b h1 h2 h3 => hstep q b (by omega) (by omega) h3)
        (fun b hb => hend b (by rwa [e])) (hs.1 b' hf)

theorem forIn_range_break {β : Type} (I : ℕ → β → Prop) (Q : β → Prop)
    (f : ℕ → β → Id (ForInStep β)) (n : ℕ) (b : β)
    (hstep : ∀ q b, q < n → I q b →
      (∀ b', f q b = ForInStep.yield b' → I (q + 1) b') ∧
        (∀ b', f q b = ForInStep.done b' → Q b'))
    (hend : ∀ b, I n b → Q b) (h0 : I 0 b) : Q (forIn (m := Id) [:n] b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : Std.Legacy.Range.size [:n] = n := by simp [Std.Legacy.Range.size]
  simp only [hs]
  exact forIn_range'_break I Q f n 0 b (fun q b _ h2 h3 => hstep q b (by omega) h3)
    (fun b hb => hend b (by simpa using hb)) h0

theorem forIn_range_yield {β : Type} (I : ℕ → β → Prop) (f : ℕ → β → Id (ForInStep β))
    (n : ℕ) (b : β) (hstep : ∀ q b, q < n → I q b → ∃ b', f q b = ForInStep.yield b' ∧
      I (q + 1) b') (h0 : I 0 b) : I n (forIn (m := Id) [:n] b f) := by
  refine forIn_range_break I (I n) f n b (fun q b hq hI => ⟨fun b' hb' => ?_, fun b' hb' => ?_⟩)
    (fun _ h => h) h0
  · obtain ⟨b'', h1, h2⟩ := hstep q b hq hI
    rw [h1] at hb'
    cases hb'
    exact h2
  · obtain ⟨b'', h1, -⟩ := hstep q b hq hI
    rw [h1] at hb'
    cases hb'

theorem get!_push_lt {α : Type} [Inhabited α] (xs : Array α) (x : α) {i : ℕ}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by rw [Array.size_push]; omega), getElem!_pos xs i h,
    Array.getElem_push_lt h]

theorem get!_push_eq {α : Type} [Inhabited α] (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem get!_set!_eq {α : Type} [Inhabited α] (a : Array α) (k r : ℕ) (v : α) (hr : r < a.size) :
    (a.set! k v)[r]! = if k = r then v else a[r]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (a.setIfInBounds k v) r (by simpa using hr),
    Array.getElem_setIfInBounds hr, getElem!_pos a r hr]

theorem size_set!' {α : Type} (a : Array α) (k : ℕ) (v : α) : (a.set! k v).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem compA_size (n : ℕ) (t u : Array ℕ) : (compA n t u).size = n := by
  simp [compA]

theorem idA_size (n : ℕ) : (idA n).size = n := by
  simp [idA]

theorem arr_eq_of_rep {n : ℕ} {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : t.size = n)
    (hu : u.size = n) (htg : Rep n t g) (hug : Rep n u g) : t = u := by
  refine Array.ext (by rw [ht, hu]) fun i h1 h2 => ?_
  have hi : i < n := ht ▸ h1
  have e1 := htg.apply hi
  have e2 := hug.apply hi
  rw [getElem!_pos t i h1] at e1
  rw [getElem!_pos u i h2] at e2
  rw [e1, e2]

theorem arr_eq_of_eqA {n : ℕ} {t u : Array ℕ} (ht : t.size = n) (hu : u.size = n)
    (h : eqA n t u = true) : t = u := by
  rw [eqA, allLt_iff] at h
  refine Array.ext (by rw [ht, hu]) fun i h1 h2 => ?_
  have := h i (ht ▸ h1)
  rw [beq_iff_eq, getElem!_pos t i h1, getElem!_pos u i h2] at this
  exact this

theorem eqA_self (n : ℕ) (t : Array ℕ) : eqA n t t = true := by
  rw [eqA, allLt_iff]
  intro i _
  exact beq_self_eq_true _

@[expose] def idxMap (E : Array (Array ℕ)) (m : ℕ) : Std.HashMap (Array ℕ) ℕ :=
  forIn (m := Id) [:m] ({} : Std.HashMap (Array ℕ) ℕ) fun i idx =>
    pure (ForInStep.yield (idx.insert E[i]! i))

theorem idxMap_spec {E : Array (Array ℕ)} {m : ℕ}
    (hinj : ∀ i < m, ∀ j < m, E[i]! = E[j]! → i = j) :
    (∀ i < m, (idxMap E m)[E[i]!]? = some i) ∧
      ∀ y i, (idxMap E m)[y]? = some i → i < m ∧ E[i]! = y := by
  unfold idxMap
  refine forIn_range_yield (fun q (idx : Std.HashMap (Array ℕ) ℕ) =>
      (∀ i < q, idx[E[i]!]? = some i) ∧ ∀ y i, idx[y]? = some i → i < q ∧ E[i]! = y)
    _ m _ (fun q idx hq hI => ⟨_, rfl, fun i hi => ?_, fun y i hy => ?_⟩) ⟨fun i hi => by omega,
      fun y i hy => by simp at hy⟩
  · rw [Std.HashMap.getElem?_insert]
    rcases Nat.lt_or_ge i q with h1 | h1
    · have hne : (E[q]! == E[i]!) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        have := hinj q hq i (by omega) e
        omega
      rw [hne]
      exact hI.1 i h1
    · have e : i = q := by omega
      rw [e, beq_self_eq_true, if_pos rfl]
  · rw [Std.HashMap.getElem?_insert] at hy
    split_ifs at hy with hz
    · cases hy
      exact ⟨by omega, beq_iff_eq.1 hz⟩
    · have := hI.2 y i hy
      exact ⟨by omega, this.2⟩

theorem csNxt_spec (n : ℕ) (gens E : Array (Array ℕ)) (idx : Std.HashMap (Array ℕ) ℕ) :
    (csNxt n gens E idx).size = E.size * gens.size ∧
      ∀ i < E.size, ∀ k < gens.size, (csNxt n gens E idx)[i * gens.size + k]! =
        idx.getD (compA n gens[k]! E[i]!) E.size := by
  have hlt : ∀ i < E.size, ∀ k < gens.size, i * gens.size + k < E.size * gens.size := by
    intro i hi k hk
    calc i * gens.size + k < i * gens.size + gens.size := by omega
      _ = (i + 1) * gens.size := by rw [Nat.succ_mul]
      _ ≤ E.size * gens.size := Nat.mul_le_mul_right _ hi
  unfold csNxt
  refine forIn_range_yield (fun q (a : Array ℕ) => a.size = E.size * gens.size ∧
      ∀ i < q, ∀ k < gens.size, a[i * gens.size + k]! = idx.getD (compA n gens[k]! E[i]!) E.size)
    _ E.size _ (fun q a hq hI => ⟨_, rfl, ?_⟩) ⟨by simp, fun i hi => by omega⟩
  · have inner := forIn_range_yield (fun r (b : Array ℕ) => b.size = E.size * gens.size ∧
        (∀ i < q, ∀ k < gens.size, b[i * gens.size + k]! =
          idx.getD (compA n gens[k]! E[i]!) E.size) ∧
        ∀ k < r, b[q * gens.size + k]! = idx.getD (compA n gens[k]! E[q]!) E.size)
      (csRow n gens E idx q) gens.size a (fun r b hr hJ => ⟨_, rfl, ?_⟩)
      ⟨hI.1, hI.2, fun k hk => by omega⟩
    · refine ⟨inner.1, fun i hi k hk => ?_⟩
      rcases Nat.lt_or_ge i q with h1 | h1
      · exact inner.2.1 i h1 k hk
      · have e : i = q := by omega
        subst e
        exact inner.2.2 k hk
    · obtain ⟨hs, hold, hnew⟩ := hJ
      refine ⟨by rw [size_set!', hs], fun i hi k hk => ?_, fun k hk => ?_⟩
      · rw [get!_set!_eq _ _ _ _ (by rw [hs]; exact hlt i (by omega) k hk), if_neg ?_]
        · exact hold i hi k hk
        · intro e
          have h1 : i * gens.size + k < (i + 1) * gens.size := by rw [Nat.succ_mul]; omega
          have h2 : (i + 1) * gens.size ≤ q * gens.size := Nat.mul_le_mul_right _ hi
          omega
      · rw [get!_set!_eq _ _ _ _ (by rw [hs]; exact hlt q hq k (by omega))]
        split_ifs with e
        · have : r = k := by omega
          rw [this]
        · exact hnew k (by omega)

section Complete

variable {n : ℕ} {gens : Array (Array ℕ)} {Gs : ℕ → Equiv.Perm (Fin n)}

@[expose] def GInv (n : ℕ) (gens : Array (Array ℕ)) (Gs : ℕ → Equiv.Perm (Fin n))
    (E : Array (Array ℕ)) (par gen : Array ℕ) (idx : Std.HashMap (Array ℕ) ℕ) : Prop :=
  0 < E.size ∧ E[0]! = idA n ∧ par.size = E.size ∧ gen.size = E.size ∧
    (∀ i < E.size, E[i]!.size = n ∧ ∃ g ∈ gensClosure gens Gs, Rep n E[i]! g) ∧
    (∀ i < E.size, i ≠ 0 → par[i]! < i ∧ gen[i]! < gens.size ∧
      E[i]! = compA n gens[gen[i]!]! E[par[i]!]!) ∧
    (∀ i < E.size, idx[E[i]!]? = some i) ∧ ∀ y i, idx[y]? = some i → i < E.size ∧ E[i]! = y

theorem ginv_init : GInv n gens Gs #[idA n] #[0] #[0]
    (({} : Std.HashMap (Array ℕ) ℕ).insert (idA n) 0) := by
  refine ⟨by simp, rfl, rfl, rfl, fun i hi => ?_, fun i hi h0 => ?_, fun i hi => ?_,
    fun y i hy => ?_⟩
  · have e : i = 0 := by simpa using hi
    subst e
    exact ⟨idA_size n, 1, Subgroup.one_mem _, rep_idA⟩
  · have e : i = 0 := by simpa using hi
    exact absurd e h0
  · have e : i = 0 := by simpa using hi
    subst e
    simp
  · rw [Std.HashMap.getElem?_insert] at hy
    split_ifs at hy with hz
    · cases hy
      exact ⟨by simp, beq_iff_eq.1 hz⟩
    · simp at hy

theorem ginv_inj {E : Array (Array ℕ)} {par gen : Array ℕ} {idx : Std.HashMap (Array ℕ) ℕ}
    (H : GInv n gens Gs E par gen idx) : ∀ i < E.size, ∀ j < E.size, E[i]! = E[j]! → i = j := by
  intro i hi j hj e
  have h1 := H.2.2.2.2.2.2.1 i hi
  rw [e, H.2.2.2.2.2.2.1 j hj] at h1
  exact (Option.some.inj h1).symm

theorem ginv_push (hgens : ∀ k < gens.size, Rep n gens[k]! (Gs k)) {E : Array (Array ℕ)}
    {par gen : Array ℕ} {idx : Std.HashMap (Array ℕ) ℕ} (H : GInv n gens Gs E par gen idx)
    {h k : ℕ} (hh : h < E.size) (hk : k < gens.size)
    (hnew : idx.contains (compA n gens[k]! E[h]!) = false) :
    GInv n gens Gs (E.push (compA n gens[k]! E[h]!)) (par.push h) (gen.push k)
      (idx.insert (compA n gens[k]! E[h]!) E.size) := by
  obtain ⟨hpos, h0, hps, hgs, hrep, hpar, hi1, hi2⟩ := H
  set y := compA n gens[k]! E[h]! with hy
  have hne : ∀ i < E.size, (y == E[i]!) = false := by
    intro i hi
    rw [beq_eq_false_iff_ne]
    intro e
    rw [Std.HashMap.contains_eq_isSome_getElem?, e, hi1 i hi] at hnew
    exact Bool.noConfusion hnew
  have hsz : (E.push y).size = E.size + 1 := Array.size_push _
  refine ⟨by rw [hsz]; omega, by rw [get!_push_lt _ _ hpos, h0], by rw [Array.size_push, hps, hsz],
    by rw [Array.size_push, hgs, hsz], fun i hi => ?_, fun i hi hi0 => ?_, fun i hi => ?_,
    fun z i hz => ?_⟩
  · rw [hsz] at hi
    rcases Nat.lt_or_ge i E.size with h1 | h1
    · rw [get!_push_lt _ _ h1]
      exact hrep i h1
    · have e : i = E.size := by omega
      rw [e, get!_push_eq]
      obtain ⟨g, hg, hgr⟩ := (hrep h hh).2
      exact ⟨compA_size _ _ _, Gs k * g,
        Subgroup.mul_mem _ (Subgroup.subset_closure ⟨k, hk, rfl⟩) hg, rep_compA (hgens k hk) hgr⟩
  · rw [hsz] at hi
    rcases Nat.lt_or_ge i E.size with h1 | h1
    · rw [get!_push_lt _ _ (by rw [hps]; exact h1), get!_push_lt _ _ (by rw [hgs]; exact h1),
        get!_push_lt _ _ h1]
      obtain ⟨a, b, c⟩ := hpar i h1 hi0
      rw [get!_push_lt _ _ (lt_trans a h1)]
      exact ⟨a, b, c⟩
    · have e : i = E.size := by omega
      subst e
      rw [← hps, get!_push_eq, hps, ← hgs, get!_push_eq, hgs, get!_push_eq, get!_push_lt _ _ hh]
      exact ⟨hh, hk, rfl⟩
  · rw [Std.HashMap.getElem?_insert]
    rw [hsz] at hi
    rcases Nat.lt_or_ge i E.size with h1 | h1
    · rw [get!_push_lt _ _ h1, hne i h1]
      exact hi1 i h1
    · have e : i = E.size := by omega
      rw [e, get!_push_eq, beq_self_eq_true, if_pos rfl]
  · rw [Std.HashMap.getElem?_insert] at hz
    split_ifs at hz with h2
    · cases hz
      rw [hsz, get!_push_eq]
      exact ⟨by omega, beq_iff_eq.1 h2⟩
    · obtain ⟨a, b⟩ := hi2 z i hz
      rw [hsz, get!_push_lt _ _ a]
      exact ⟨by omega, b⟩

theorem ginv_size_le {E : Array (Array ℕ)} {par gen : Array ℕ} {idx : Std.HashMap (Array ℕ) ℕ}
    (H : GInv n gens Gs E par gen idx) :
    E.size ≤ Nat.card (gensClosure gens Gs) := by
  have hrep := H.2.2.2.2.1
  let f : Fin E.size → gensClosure gens Gs := fun i =>
    ⟨((hrep i i.2).2).choose, ((hrep i i.2).2).choose_spec.1⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hg := congrArg Subtype.val hij
    have hi := ((hrep i i.2).2).choose_spec.2
    have hj := ((hrep j j.2).2).choose_spec.2
    simp only [f] at hg
    rw [hg] at hi
    exact Fin.ext (ginv_inj H i i.2 j j.2
      (arr_eq_of_rep (hrep i i.2).1 (hrep j j.2).1 hi hj))
  have := Nat.card_le_card_of_injective f hinj
  simpa using this

theorem contains_insert_of {idx : Std.HashMap (Array ℕ) ℕ} {y z : Array ℕ} {v : ℕ}
    (h : idx.contains z = true) : (idx.insert y v).contains z = true := by
  rw [Std.HashMap.contains_insert, h, Bool.or_true]

theorem inner_spec (hgens : ∀ k < gens.size, Rep n gens[k]! (Gs k)) {E : Array (Array ℕ)}
    {par gen : Array ℕ} {idx : Std.HashMap (Array ℕ) ℕ} (H : GInv n gens Gs E par gen idx)
    {h : ℕ} (hh : h < E.size) :
    have r : KSt := forIn (m := Id) [:gens.size] (E, par, gen, idx) (csInner n gens h E[h]!)
    GInv n gens Gs r.1 r.2.1 r.2.2.1 r.2.2.2 ∧ E.size ≤ r.1.size ∧
      (∀ i < E.size, r.1[i]! = E[i]!) ∧
      (∀ z, idx.contains z = true → r.2.2.2.contains z = true) ∧
      ∀ k < gens.size, r.2.2.2.contains (compA n gens[k]! E[h]!) = true := by
  refine forIn_range_yield (fun q (s : KSt) => GInv n gens Gs s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
      E.size ≤ s.1.size ∧ (∀ i < E.size, s.1[i]! = E[i]!) ∧
      (∀ z, idx.contains z = true → s.2.2.2.contains z = true) ∧
      ∀ k < q, s.2.2.2.contains (compA n gens[k]! E[h]!) = true)
    (csInner n gens h E[h]!) gens.size (E, par, gen, idx) (fun q s hq hI => ?_)
    ⟨H, le_refl _, fun i _ => rfl, fun z hz => hz, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  obtain ⟨hG, hle, hpre, hmono, hdone⟩ := hI
  have hx : s.1[h]! = E[h]! := hpre h hh
  cases hc : s.2.2.2.contains (compA n gens[q]! E[h]!) with
  | true =>
    refine ⟨s, ?_, hG, hle, hpre, hmono, fun k hk => ?_⟩
    · unfold csInner
      rw [hc]
      rfl
    · rcases Nat.lt_or_ge k q with h1 | h1
      · exact hdone k h1
      · have e : k = q := by omega
        rw [e]
        exact hc
  | false =>
    refine ⟨(s.1.push (compA n gens[q]! E[h]!), s.2.1.push h, s.2.2.1.push q,
      s.2.2.2.insert (compA n gens[q]! E[h]!) s.1.size), ?_, ?_, ?_, fun i hi => ?_,
      fun z hz => contains_insert_of (hmono z hz), fun k hk => ?_⟩
    · unfold csInner
      rw [hc]
      rfl
    · have := ginv_push hgens hG (lt_of_lt_of_le hh hle) hq (by rw [hx]; exact hc)
      rw [hx] at this
      exact this
    · rw [Array.size_push]
      omega
    · rw [get!_push_lt _ _ (by omega)]
      exact hpre i hi
    · rcases Nat.lt_or_ge k q with h1 | h1
      · exact contains_insert_of (hdone k h1)
      · have e : k = q := by omega
        rw [e, Std.HashMap.contains_insert, beq_self_eq_true, Bool.true_or]

theorem closureSearch_spec (hgens : ∀ k < gens.size, Rep n gens[k]! (Gs k)) {bound : ℕ}
    (hb : Nat.card (gensClosure gens Gs) ≤ bound) :
    closureOK n gens (closureSearch n gens bound).1 (closureSearch n gens bound).2.1
        (closureSearch n gens bound).2.2.1 (closureSearch n gens bound).2.2.2 = true ∧
      (∀ i < (closureSearch n gens bound).1.size, ((closureSearch n gens bound).1)[i]!.size = n) ∧
      ∀ i < (closureSearch n gens bound).1.size, ∀ j < (closureSearch n gens bound).1.size,
        ((closureSearch n gens bound).1)[i]! = ((closureSearch n gens bound).1)[j]! → i = j := by
  have key : ∀ s : CSt, GInv n gens Gs s.1 s.2.1 s.2.2.1 s.2.2.2.1 ∧ s.2.2.2.2 = s.1.size ∧
      (∀ h < s.1.size, ∀ k < gens.size, s.2.2.2.1.contains (compA n gens[k]! s.1[h]!) = true) →
      closureOK n gens s.1 s.2.1 s.2.2.1 (csNxt n gens s.1 s.2.2.2.1) = true ∧
        (∀ i < s.1.size, (s.1)[i]!.size = n) ∧
        ∀ i < s.1.size, ∀ j < s.1.size, (s.1)[i]! = (s.1)[j]! → i = j := by
    rintro ⟨E, par, gen, idx, head⟩ ⟨H, -, hcl⟩
    dsimp only at H hcl ⊢
    have hinj := ginv_inj H
    obtain ⟨hpos, h0, -, -, hrep, hpar, hi1, hi2⟩ := H
    obtain ⟨-, hnx⟩ := csNxt_spec n gens E idx
    refine ⟨?_, fun i hi => (hrep i hi).1, hinj⟩
    unfold closureOK
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hpos, by rw [h0]; exact eqA_self _ _⟩, allLt_iff.2 fun i hi => ?_⟩,
      allLt_iff.2 fun i hi => allLt_iff.2 fun k hk => ?_⟩
    · by_cases hi0 : i = 0
      · simp [hi0]
      · obtain ⟨a, b, c⟩ := hpar i hi hi0
        simp only [Bool.or_eq_true, beq_iff_eq, hi0, false_or, Bool.and_eq_true,
          decide_eq_true_eq]
        rw [← c]
        exact ⟨⟨a, b⟩, eqA_self _ _⟩
    · have hc := hcl i hi k hk
      rw [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists] at hc
      obtain ⟨j, hj⟩ := hc
      obtain ⟨hjs, hje⟩ := hi2 _ j hj
      rw [hnx i hi k hk, Std.HashMap.getD_eq_getD_getElem?, hj, Option.getD_some]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [hje]
      exact ⟨hjs, eqA_self _ _⟩
  rw [closureSearch_eq_cs]
  refine key _ (forIn_range_break (fun q (s : CSt) => GInv n gens Gs s.1 s.2.1 s.2.2.1 s.2.2.2.1 ∧
      s.2.2.2.2 = q ∧ q ≤ s.1.size ∧
      ∀ h < q, ∀ k < gens.size, s.2.2.2.1.contains (compA n gens[k]! s.1[h]!) = true)
    (fun s => GInv n gens Gs s.1 s.2.1 s.2.2.1 s.2.2.2.1 ∧ s.2.2.2.2 = s.1.size ∧
      ∀ h < s.1.size, ∀ k < gens.size, s.2.2.2.1.contains (compA n gens[k]! s.1[h]!) = true)
    (csOuter n gens) bound (csInit n) (fun q s hq hI => ?_) (fun s hI => ?_) ?_)
  · obtain ⟨E, par, gen, idx, head⟩ := s
    obtain ⟨hG, hhead, hqE, hcl⟩ := hI
    dsimp only at hG hhead hqE hcl
    subst hhead
    by_cases hlt : head < E.size
    · have hr := inner_spec hgens hG hlt
      refine ⟨fun b' hb' => ?_, fun b' hb' => ?_⟩
      · simp only [csOuter, hlt, ↓reduceIte] at hb'
        cases hb'
        obtain ⟨hG', hle, hpre, hmono, hnew⟩ := hr
        refine ⟨hG', rfl, by dsimp only; omega, fun h hh k hk => ?_⟩
        rcases Nat.lt_or_ge h head with h1 | h1
        · rw [hpre h (by omega)]
          exact hmono _ (hcl h h1 k hk)
        · have e : h = head := by omega
          rw [e, hpre head hlt]
          exact hnew k hk
      · simp only [csOuter, hlt, ↓reduceIte] at hb'
        cases hb'
    · refine ⟨fun b' hb' => ?_, fun b' hb' => ?_⟩
      · simp only [csOuter, hlt, ↓reduceIte] at hb'
        cases hb'
      · simp only [csOuter, hlt, ↓reduceIte] at hb'
        cases hb'
        have e : head = E.size := by omega
        exact ⟨hG, e, fun h hh k hk => hcl h (by dsimp only at hh; omega) k hk⟩
  · obtain ⟨hG, hhead, hqE, hcl⟩ := hI
    have hle := ginv_size_le hG
    have e : s.1.size = bound := by omega
    exact ⟨hG, by omega, fun h hh k hk => hcl h (by omega) k hk⟩
  · exact ⟨ginv_init, rfl, Nat.zero_le _, fun h hh => absurd hh (Nat.not_lt_zero _)⟩

theorem closureSearch_size (hgens : ∀ k < gens.size, Rep n gens[k]! (Gs k)) {bound : ℕ}
    (hb : Nat.card (gensClosure gens Gs) ≤ bound) :
    (closureSearch n gens bound).1.size = Nat.card (gensClosure gens Gs) := by
  obtain ⟨hok, hsz, hinj⟩ := closureSearch_spec hgens hb
  set E := (closureSearch n gens bound).1
  have hrec := exists_rep_mem_closure hgens hok
  let f : Fin E.size → gensClosure gens Gs := fun i =>
    ⟨(hrec i i.2).choose, (hrec i i.2).choose_spec.1⟩
  have hinjf : Function.Injective f := by
    intro i j hij
    have hg := congrArg Subtype.val hij
    have hi := (hrec i i.2).choose_spec.2
    have hj := (hrec j j.2).choose_spec.2
    simp only [f] at hg
    rw [hg] at hi
    exact Fin.ext (hinj i i.2 j j.2 (arr_eq_of_rep (hsz i i.2) (hsz j j.2) hi hj))
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨i, hi, hig⟩ := exists_rep_of_mem_closure hgens hok hg
    exact ⟨⟨i, hi⟩, Subtype.ext ((hrec i hi).choose_spec.2.unique hig)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinjf, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_fin]

end Complete

end CFSG.Sporadic.FischerOddCore.SearchSpec

end
