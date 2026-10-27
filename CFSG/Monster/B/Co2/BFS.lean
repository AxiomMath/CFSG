module

public import CFSG.Certificates.SchreierOrbitSearchInvariants

public section

namespace CFSG.Monster.B.Co2

open CFSG.Certificates CFSG.Certificates.SchreierOrbitState

variable {n : ℕ}

@[expose] def LexLt (a b c d : ℕ) : Prop := a < c ∨ (a = c ∧ b < d)

theorem lexLt_trans {a b c d e f : ℕ} (h₁ : LexLt a b c d) (h₂ : LexLt c d e f) :
    LexLt a b e f := by
  unfold LexLt at *
  omega

structure BFSCert (steps : List (Equiv.Perm (Fin n))) (b : Fin n) (m : ℕ) (pts : ℕ → Fin n)
    (par lab : ℕ → ℕ) (T : ℕ → Equiv.Perm (Fin n)) : Prop where
  pos : 0 < m
  root : pts 0 = b
  T_zero : T 0 = 1
  inj : ∀ i < m, ∀ j < m, pts i = pts j → i = j
  par_lt : ∀ k, 0 < k → k < m → par k < k
  lab_lt : ∀ k, 0 < k → k < m → lab k < steps.length
  edge : ∀ k (hk : 0 < k) (hkm : k < m), (steps[lab k]'(lab_lt k hk hkm)) (pts (par k)) = pts k
  T_step : ∀ k (hk : 0 < k) (hkm : k < m), T k = (steps[lab k]'(lab_lt k hk hkm)) * T (par k)
  mono : ∀ k, 0 < k → k + 1 < m → LexLt (par k) (lab k) (par (k + 1)) (lab (k + 1))
  closed : ∀ h < m, ∀ j (hj : j < steps.length), ∃ k < m, pts k = steps[j] (pts h) ∧
    (k = 0 ∨ ¬ LexLt h j (par k) (lab k))

namespace BFSCert

variable {steps : List (Equiv.Perm (Fin n))} {b : Fin n} {m : ℕ} {pts : ℕ → Fin n}
  {par lab : ℕ → ℕ} {T : ℕ → Equiv.Perm (Fin n)}

theorem mono_lt (hC : BFSCert steps b m pts par lab T) :
    ∀ a c, 0 < a → a < c → c < m → LexLt (par a) (lab a) (par c) (lab c) := by
  intro a c ha hac hc
  induction c with
  | zero => omega
  | succ c ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hac with h | h
    · exact lexLt_trans (ih h (by omega)) (hC.mono c (by omega) hc)
    · subst h
      exact hC.mono a ha hc

@[expose] def recs (pts : ℕ → Fin n) (T : ℕ → Equiv.Perm (Fin n)) (c : ℕ) :
    List (Fin n × Equiv.Perm (Fin n)) :=
  (List.range c).map fun k => (pts k, T k)

@[expose] def pend (pts : ℕ → Fin n) (h c : ℕ) : List (Fin n) := ((List.range c).drop h).map pts

theorem recs_succ (c : ℕ) : recs pts T (c + 1) = recs pts T c ++ [(pts c, T c)] := by
  simp [recs, List.range_succ]

theorem pend_succ {h c : ℕ} (hc : h ≤ c) : pend pts h (c + 1) = pend pts h c ++ [pts c] := by
  simp only [pend, List.range_succ]
  rw [List.drop_append_of_le_length (by simpa using hc)]
  simp

theorem pend_cons {h c : ℕ} (hc : h < c) : pend pts h c = pts h :: pend pts (h + 1) c := by
  simp only [pend]
  rw [List.drop_eq_getElem_cons (by simpa using hc)]
  simp

theorem pend_self (c : ℕ) : pend pts c c = [] := by
  simp [pend]

theorem lookup_recs_of_lt (hC : BFSCert steps b m pts par lab T) {c k : ℕ} (hcm : c ≤ m)
    (hk : k < c) : (recs pts T c).lookup (pts k) = some (T k) := by
  induction c with
  | zero => omega
  | succ c ih =>
    rw [recs_succ, List.lookup_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · rw [ih (by omega) h]
      rfl
    · subst h
      have hnone : (recs pts T k).lookup (pts k) = none := by
        rw [List.lookup_eq_none_iff]
        intro p hp
        simp only [recs, List.mem_map, List.mem_range] at hp
        obtain ⟨k', hk', rfl⟩ := hp
        rw [bne_iff_ne]
        intro he
        have := hC.inj k' (by omega) k (by omega) he.symm
        omega
      rw [hnone]
      simp [List.lookup]

theorem lookup_recs_eq_none (hC : BFSCert steps b m pts par lab T) {c k : ℕ} (_hcm : c ≤ m)
    (hk : k < m) (hkc : c ≤ k) : (recs pts T c).lookup (pts k) = none := by
  rw [List.lookup_eq_none_iff]
  intro p hp
  simp only [recs, List.mem_map, List.mem_range] at hp
  obtain ⟨k', hk', rfl⟩ := hp
  rw [bne_iff_ne]
  intro he
  have := hC.inj k' (by omega) k hk he.symm
  omega

@[expose] def Good (m : ℕ) (par lab : ℕ → ℕ) (h j c : ℕ) : Prop :=
  1 ≤ c ∧ c ≤ m ∧ ∀ k, 0 < k → k < m → (k < c ↔ LexLt (par k) (lab k) h j)

theorem lexLt_succ_iff {a d h j : ℕ} : LexLt a d h (j + 1) ↔ LexLt a d h j ∨ (a = h ∧ d = j) := by
  unfold LexLt
  omega

theorem discover_good (hC : BFSCert steps b m pts par lab T) {h j c : ℕ} (hhm : h < m)
    (hj : j < steps.length) (hgood : Good m par lab h j c) (hhc : h < c) :
    ∃ c', Good m par lab h (j + 1) c' ∧ h < c' ∧
      (⟨recs pts T c, pend pts (h + 1) c⟩ : SchreierOrbitState n).discover
        (steps[j] (pts h)) (steps[j] * T h) = ⟨recs pts T c', pend pts (h + 1) c'⟩ := by
  obtain ⟨hc1, hcm, hiff⟩ := hgood
  obtain ⟨k, hkm, hk, hkle⟩ := hC.closed h hhm j hj
  have hsame : ∀ k', 0 < k' → k' < m → par k' = h → lab k' = j → k' = k := by
    intro k' hk'0 hk'm hp hl
    refine hC.inj k' hk'm k hkm ?_
    rw [← hC.edge k' hk'0 hk'm, hk]
    simp only [hp, hl]
  by_cases hkc : k < c
  · refine ⟨c, ⟨hc1, hcm, fun k' hk'0 hk'm => ?_⟩, hhc, ?_⟩
    · rw [lexLt_succ_iff, ← hiff k' hk'0 hk'm]
      constructor
      · exact Or.inl
      · rintro (h' | ⟨hp, hl⟩)
        · exact h'
        · rw [hsame k' hk'0 hk'm hp hl]
          exact hkc
    · rw [← hk]
      apply discover_of_assigned
      change ((recs pts T c).lookup (pts k)).isSome = true
      rw [hC.lookup_recs_of_lt hcm hkc]
      rfl
  · have hk0 : k ≠ 0 := by omega
    have hle : ¬ LexLt h j (par k) (lab k) := hkle.resolve_left hk0
    have hnlt : ¬ LexLt (par k) (lab k) h j := fun hl => hkc ((hiff k (by omega) hkm).2 hl)
    have hpk : par k = h := by unfold LexLt at hle hnlt; omega
    have hlk : lab k = j := by unfold LexLt at hle hnlt; omega
    have hkc' : k = c := by
      by_contra hne
      have hck : c < k := by omega
      have := hC.mono_lt c k (by omega) hck hkm
      rw [hpk, hlk] at this
      exact absurd ((hiff c (by omega) (by omega)).2 this) (lt_irrefl c)
    subst hkc'
    refine ⟨k + 1, ⟨by omega, hkm, fun k' hk'0 hk'm => ?_⟩, by omega, ?_⟩
    · rw [lexLt_succ_iff, ← hiff k' hk'0 hk'm]
      constructor
      · intro hk'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h' ▸ hpk, h' ▸ hlk⟩
      · rintro (h' | ⟨hp, hl⟩)
        · omega
        · rw [hsame k' hk'0 hk'm hp hl]
          omega
    · have hn : (⟨recs pts T k, pend pts (h + 1) k⟩ : SchreierOrbitState n).transversal? (pts k) =
          none := hC.lookup_recs_eq_none hcm hkm le_rfl
      rw [← hk, discover_of_unassigned _ _ _ hn]
      have hT : steps[j] * T h = T k := by
        rw [hC.T_step k (by omega) hkm]
        simp only [hpk, hlk]
      rw [hT, recs_succ, pend_succ (by omega)]

theorem fold_good (hC : BFSCert steps b m pts par lab T) {h : ℕ} (hhm : h < m) :
    ∀ d j c, j + d = steps.length → Good m par lab h j c → h < c →
      ∃ c', Good m par lab h steps.length c' ∧ h < c' ∧
        (steps.drop j).foldl (fun state s => state.discover (s (pts h)) (s * T h))
          (⟨recs pts T c, pend pts (h + 1) c⟩ : SchreierOrbitState n) =
          ⟨recs pts T c', pend pts (h + 1) c'⟩ := by
  intro d
  induction d with
  | zero =>
    intro j c hj hg hhc
    refine ⟨c, ?_, hhc, ?_⟩
    · rwa [← hj, Nat.add_zero]
    · rw [List.drop_eq_nil_of_le (by omega)]
      rfl
  | succ d ih =>
    intro j c hj hg hhc
    have hjl : j < steps.length := by omega
    obtain ⟨c', hg', hhc', he⟩ := hC.discover_good hhm hjl hg hhc
    obtain ⟨c'', hg'', hhc'', he'⟩ := ih (j + 1) c' (by omega) hg' hhc'
    refine ⟨c'', hg'', hhc'', ?_⟩
    rw [List.drop_eq_getElem_cons hjl, List.foldl_cons, he, he']

theorem good_next {h c : ℕ} (hC : BFSCert steps b m pts par lab T)
    (hg : Good m par lab h steps.length c) : Good m par lab (h + 1) 0 c := by
  obtain ⟨hc1, hcm, hiff⟩ := hg
  refine ⟨hc1, hcm, fun k hk0 hkm => ?_⟩
  rw [hiff k hk0 hkm]
  have := hC.lab_lt k hk0 hkm
  unfold LexLt
  omega

theorem step_good (hC : BFSCert steps b m pts par lab T) {h c : ℕ} (hhm : h < m)
    (hg : Good m par lab h 0 c) :
    ∃ c', Good m par lab (h + 1) 0 c' ∧
      step steps (⟨recs pts T c, pend pts h c⟩ : SchreierOrbitState n) =
        ⟨recs pts T c', pend pts (h + 1) c'⟩ := by
  have hhc : h < c := by
    obtain ⟨hc1, hcm, hiff⟩ := hg
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · omega
    · exact (hiff h hpos hhm).2 (Or.inl (hC.par_lt h hpos hhm))
  obtain ⟨c', hg', hhc', he⟩ := hC.fold_good hhm steps.length 0 c (by omega) hg hhc
  refine ⟨c', hC.good_next hg', ?_⟩
  have htx : (recs pts T c).lookup (pts h) = some (T h) := hC.lookup_recs_of_lt hg.2.1 hhc
  simp only [step, pend_cons hhc, transversal?, htx, Option.getD_some]
  simpa using he

theorem run_good (hC : BFSCert steps b m pts par lab T) :
    ∀ h ≤ m, ∃ c, Good m par lab h 0 c ∧
      run steps h (initial b) = (⟨recs pts T c, pend pts h c⟩ : SchreierOrbitState n) := by
  intro h
  induction h with
  | zero =>
    intro _
    refine ⟨1, ⟨le_rfl, hC.pos, fun k hk0 hkm => ?_⟩, ?_⟩
    · unfold LexLt
      omega
    · simp [run, initial, recs, pend, hC.root, hC.T_zero]
  | succ h ih =>
    intro hh
    obtain ⟨c, hg, he⟩ := ih (by omega)
    obtain ⟨c', hg', he'⟩ := hC.step_good (by omega) hg
    refine ⟨c', hg', ?_⟩
    rw [run_append_iterations steps h 1, he, run_succ, run_zero, he']

theorem m_le (hC : BFSCert steps b m pts par lab T) : m ≤ n := by
  have hinj : Function.Injective fun k : Fin m => pts k := fun i j h =>
    Fin.ext (hC.inj i i.2 j j.2 h)
  simpa using Fintype.card_le_of_injective _ hinj

theorem run_initial_eq (hC : BFSCert steps b m pts par lab T) :
    run steps n (initial b) =
      (⟨(List.range m).map fun k => (pts k, T k), []⟩ : SchreierOrbitState n) := by
  obtain ⟨c, ⟨hc1, hcm, hiff⟩, he⟩ := hC.run_good m le_rfl
  have hcm' : c = m := by
    refine le_antisymm hcm ?_
    by_contra hlt
    have hm : 1 < m := by omega
    have := (hiff (m - 1) (by omega) (by omega)).2 (Or.inl (by
      have := hC.par_lt (m - 1) (by omega) (by omega)
      omega))
    omega
  subst hcm'
  have hmn := hC.m_le
  rw [congrArg (fun k => run steps k (initial b)) (show n = c + (n - c) by omega),
    run_append_iterations, he, pend_self, run_of_queue_empty _ _ _ rfl]
  rfl

end BFSCert

end CFSG.Monster.B.Co2
