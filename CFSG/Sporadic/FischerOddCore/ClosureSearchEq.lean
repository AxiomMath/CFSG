module

public import CFSG.Sporadic.FischerOddCore.ClosureSearchSpec
public import Certificates.Data.Kernel.ClosBfs
import CFSG.F3.ConjBFS
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.Sporadic.FischerOddCore.SearchSpec

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore.Native
open CFSG.KC.F3Bfs CFSG.KC.ClosBfs CFSG.F3.Native.BfsSpec CFSG.KS.SporSch.LyLoop

@[expose] noncomputable def cK (gs : ℕ) (fn fp fl : ℕ → ℕ) (h c k : ℕ) : ℕ :=
  (List.range k).foldl (fun s j => bfsHit fp fl h j (fn (h * gs + j)) s) c

@[expose] noncomputable def cntC (gs : ℕ) (fn fp fl : ℕ → ℕ) (h : ℕ) : ℕ :=
  (List.range h).foldl (fun s i => closRow gs fn fp fl i s) 1

theorem cK_succ (gs : ℕ) (fn fp fl : ℕ → ℕ) (h c k : ℕ) :
    cK gs fn fp fl h c (k + 1) = bfsHit fp fl h k (fn (h * gs + k)) (cK gs fn fp fl h c k) := by
  unfold cK
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem cntC_succ (gs : ℕ) (fn fp fl : ℕ → ℕ) (h : ℕ) :
    cntC gs fn fp fl (h + 1) = if h < cntC gs fn fp fl h then
      cK gs fn fp fl h (cntC gs fn fp fl h) gs else 0 := by
  unfold cntC
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [closRow, cK, nIf_eqP, foldUp_eqP, Nat.blt_eq, Nat.add_eq, Nat.mul_eq]

theorem cK_zero_of (gs : ℕ) (fn fp fl : ℕ → ℕ) (h c : ℕ) :
    ∀ k t, cK gs fn fp fl h c k = 0 → cK gs fn fp fl h c (k + t) = 0 := by
  intro k t
  induction t with
  | zero => exact id
  | succ t ih =>
    intro e
    rw [← Nat.add_assoc, cK_succ, ih e]
    exact bfsHit_zero _ _ _ _ _

theorem cntC_zero_of (gs : ℕ) (fn fp fl : ℕ → ℕ) :
    ∀ h t, cntC gs fn fp fl h = 0 → cntC gs fn fp fl (h + t) = 0 := by
  intro h t
  induction t with
  | zero => exact id
  | succ t ih =>
    intro e
    rw [← Nat.add_assoc, cntC_succ, ih e, if_neg (Nat.not_lt_zero _)]

theorem cK_mono (gs : ℕ) (fn fp fl : ℕ → ℕ) (h c : ℕ) :
    ∀ k, cK gs fn fp fl h c k ≠ 0 → c ≤ cK gs fn fp fl h c k
  | 0, _ => le_refl _
  | k + 1, hne => by
    have h0 : cK gs fn fp fl h c k ≠ 0 := fun e => hne (cK_zero_of gs fn fp fl h c k 1 e)
    have := cK_mono gs fn fp fl h c k h0
    rw [cK_succ] at hne ⊢
    rcases bfsHit_spec hne with h1 | h1 <;> omega

theorem cK_le_of (gs : ℕ) (fn fp fl : ℕ → ℕ) (h c k : ℕ) :
    ∀ t, cK gs fn fp fl h c (k + t) ≠ 0 → cK gs fn fp fl h c k ≤ cK gs fn fp fl h c (k + t)
  | 0, _ => le_refl _
  | t + 1, hne => by
    have h0 : cK gs fn fp fl h c (k + t) ≠ 0 := fun e => hne (cK_zero_of gs fn fp fl h c _ 1 e)
    have := cK_le_of gs fn fp fl h c k t h0
    rw [← Nat.add_assoc, cK_succ] at hne ⊢
    rcases bfsHit_spec hne with h1 | h1 <;> omega

theorem cntC_mono (gs : ℕ) (fn fp fl : ℕ → ℕ) :
    ∀ h, cntC gs fn fp fl h ≠ 0 → ∀ h' ≤ h, cntC gs fn fp fl h' ≤ cntC gs fn fp fl h
  | 0, _, h', hh' => by rw [Nat.le_zero.1 hh']
  | h + 1, hne, h', hh' => by
    have h0 : cntC gs fn fp fl h ≠ 0 := fun e => hne (cntC_zero_of gs fn fp fl h 1 e)
    have hstep : cntC gs fn fp fl h ≤ cntC gs fn fp fl (h + 1) := by
      rw [cntC_succ] at hne ⊢
      split_ifs at hne ⊢ with hlt
      · exact cK_mono gs fn fp fl h _ gs hne
      · exact absurd rfl hne
    rcases Nat.lt_or_ge h' (h + 1) with h1 | h1
    · exact le_trans (cntC_mono gs fn fp fl h h0 h' (by omega)) hstep
    · rw [show h' = h + 1 by omega]

@[expose] def RInv (E : Array (Array ℕ)) (par gen : Array ℕ) (c : ℕ) (E' : Array (Array ℕ))
    (par' gen' : Array ℕ) (idx : Std.HashMap (Array ℕ) ℕ) : Prop :=
  E'.size = c ∧ (∀ i < c, E'[i]! = E[i]!) ∧ (∀ i < c, idx[E[i]!]? = some i) ∧
    (∀ y i, idx[y]? = some i → i < c ∧ E[i]! = y) ∧ par'.size = c ∧ (∀ i < c, par'[i]! = par[i]!) ∧
    gen'.size = c ∧ ∀ i < c, gen'[i]! = gen[i]!

theorem rinv_new {E : Array (Array ℕ)} {par gen : Array ℕ} {c : ℕ} {E' : Array (Array ℕ)}
    {par' gen' : Array ℕ} {idx : Std.HashMap (Array ℕ) ℕ} (H : RInv E par gen c E' par' gen' idx)
    (hinj : ∀ i < E.size, ∀ j < E.size, E[i]! = E[j]! → i = j) (hc : c < E.size) {p l : ℕ}
    (hp : par[c]! = p) (hl : gen[c]! = l) :
    RInv E par gen (c + 1) (E'.push E[c]!) (par'.push p) (gen'.push l)
      (idx.insert E[c]! E'.size) := by
  obtain ⟨hs, hk, hi1, hi2, hps, hpk, hls, hlk⟩ := H
  have hne : ∀ i < c, (E[c]! == E[i]!) = false := by
    intro i hi
    rw [beq_eq_false_iff_ne]
    intro e
    have := hinj c hc i (by omega) e
    omega
  refine ⟨by rw [Array.size_push, hs], fun i hi => ?_, fun i hi => ?_, fun y i hy => ?_,
    by rw [Array.size_push, hps], fun i hi => ?_, by rw [Array.size_push, hls], fun i hi => ?_⟩
  · rcases Nat.lt_or_ge i c with h1 | h1
    · rw [get!_push_lt _ _ (by rw [hs]; exact h1), hk i h1]
    · have e : i = E'.size := by rw [hs]; omega
      rw [e, get!_push_eq, hs]
  · rw [Std.HashMap.getElem?_insert]
    rcases Nat.lt_or_ge i c with h1 | h1
    · rw [hne i h1]
      exact hi1 i h1
    · have e : i = c := by omega
      rw [e, beq_self_eq_true, if_pos rfl, hs]
  · rw [Std.HashMap.getElem?_insert] at hy
    split_ifs at hy with hz
    · rw [hs] at hy
      cases hy
      exact ⟨by omega, beq_iff_eq.1 hz⟩
    · have := hi2 y i hy
      exact ⟨by omega, this.2⟩
  · rcases Nat.lt_or_ge i c with h1 | h1
    · rw [get!_push_lt _ _ (by rw [hps]; exact h1), hpk i h1]
    · rw [show i = par'.size by omega, get!_push_eq, hps, hp]
  · rcases Nat.lt_or_ge i c with h1 | h1
    · rw [get!_push_lt _ _ (by rw [hls]; exact h1), hlk i h1]
    · rw [show i = gen'.size by omega, get!_push_eq, hls, hl]

theorem closureSearch_eq_of {n bound : ℕ} {gens E : Array (Array ℕ)} {par gen nxt : Array ℕ}
    {fn fp fl : ℕ → ℕ} (hok : closureOK n gens E par gen nxt = true)
    (hsz : ∀ i < E.size, E[i]!.size = n)
    (hinj : ∀ i < E.size, ∀ j < E.size, E[i]! = E[j]! → i = j) (hb : E.size ≤ bound)
    (hps : par.size = E.size) (hgs : gen.size = E.size) (hns : nxt.size = E.size * gens.size)
    (hp : ∀ i < E.size, par[i]! = fp i) (hl : ∀ i < E.size, gen[i]! = fl i)
    (hn : ∀ t < E.size * gens.size, nxt[t]! = fn t)
    (hbfs : closBfsOK gens.size fn fp fl E.size = true) :
    closureSearch n gens bound = (E, par, gen, nxt) := by
  set N := E.size with hN
  set gs := gens.size with hgsz
  obtain ⟨hpos, h0, hpar, hnxt⟩ := closureOK_facts hok
  have hE0 : E[0]! = idA n := arr_eq_of_eqA (hsz 0 hpos) (idA_size n) h0
  have hprod : ∀ i < N, ∀ k < gs, nxt[i * gs + k]! < N ∧
      E[nxt[i * gs + k]!]! = compA n gens[k]! E[i]! := by
    intro i hi k hk
    obtain ⟨a, b⟩ := hnxt i hi k hk
    exact ⟨a, arr_eq_of_eqA (hsz _ a) (compA_size _ _ _) b⟩
  have hlt : ∀ i < N, ∀ k < gs, i * gs + k < N * gs := by
    intro i hi k hk
    calc i * gs + k < i * gs + gs := by omega
      _ = (i + 1) * gs := by rw [Nat.succ_mul]
      _ ≤ N * gs := Nat.mul_le_mul_right _ hi
  simp only [closBfsOK, bAnd_eqP, Bool.and_eq_true, Nat.beq_eq] at hbfs
  obtain ⟨hp0, hl0, hfold⟩ := hbfs
  have hCN : cntC gs fn fp fl N = N := by
    rw [foldUp_eqP] at hfold
    exact hfold
  have hCne : ∀ h ≤ N, cntC gs fn fp fl h ≠ 0 := by
    intro h hh e
    have := cntC_zero_of gs fn fp fl h (N - h) e
    rw [Nat.add_sub_cancel' hh, hCN] at this
    omega
  have hCle : ∀ h ≤ N, cntC gs fn fp fl h ≤ N := by
    intro h hh
    have := cntC_mono gs fn fp fl N (hCne N le_rfl) h hh
    rwa [hCN] at this
  have hrow : ∀ q < N, q < cntC gs fn fp fl q ∧
      cntC gs fn fp fl (q + 1) = cK gs fn fp fl q (cntC gs fn fp fl q) gs := by
    intro q hq
    have hne := hCne (q + 1) (by omega)
    rw [cntC_succ] at hne ⊢
    split_ifs at hne ⊢ with h1
    · exact ⟨h1, rfl⟩
    · exact absurd rfl hne
  have hKne : ∀ q < N, ∀ k ≤ gs, cK gs fn fp fl q (cntC gs fn fp fl q) k ≠ 0 := by
    intro q hq k hk e
    have := cK_zero_of gs fn fp fl q _ k (gs - k) e
    rw [Nat.add_sub_cancel' hk, ← (hrow q hq).2] at this
    exact hCne (q + 1) (by omega) this
  have hKle : ∀ q < N, ∀ k ≤ gs, cK gs fn fp fl q (cntC gs fn fp fl q) k ≤ N := by
    intro q hq k hk
    have h1 := cK_le_of gs fn fp fl q (cntC gs fn fp fl q) k (gs - k)
      (by rw [Nat.add_sub_cancel' hk]; exact hKne q hq gs le_rfl)
    rw [Nat.add_sub_cancel' hk, ← (hrow q hq).2] at h1
    exact le_trans h1 (hCle (q + 1) (by omega))
  have hfin : ∀ s : CSt, RInv E par gen N s.1 s.2.1 s.2.2.1 s.2.2.2.1 →
      (s.1, s.2.1, s.2.2.1, csNxt n gens s.1 s.2.2.2.1) = (E, par, gen, nxt) := by
    rintro ⟨E', par', gen', idx, head⟩ ⟨hs, hk, hi1, hi2, hps', hpk, hls', hlk⟩
    dsimp only at hs hk hi1 hi2 hps' hpk hls' hlk ⊢
    have hE : E' = E := by
      refine Array.ext (by rw [hs]) fun i h1 h2 => ?_
      have := hk i (by rw [← hs]; exact h1)
      rwa [getElem!_pos _ i h1, getElem!_pos _ i h2] at this
    subst E'
    have hpar' : par' = par := by
      refine Array.ext (by rw [hps', hps]) fun i h1 h2 => ?_
      have := hpk i (by rw [← hps']; exact h1)
      rwa [getElem!_pos _ i h1, getElem!_pos _ i h2] at this
    have hgen' : gen' = gen := by
      refine Array.ext (by rw [hls', hgs]) fun i h1 h2 => ?_
      have := hlk i (by rw [← hls']; exact h1)
      rwa [getElem!_pos _ i h1, getElem!_pos _ i h2] at this
    obtain ⟨hsn, hnx⟩ := csNxt_spec n gens E idx
    rw [← hN, ← hgsz] at hsn hnx
    have hnxt' : csNxt n gens E idx = nxt := by
      refine Array.ext (by rw [hsn, hns]) fun t h1 h2 => ?_
      have hgs0 : 0 < gs := by
        rcases Nat.eq_zero_or_pos gs with e | e
        · rw [hsn, e, Nat.mul_zero] at h1
          omega
        · exact e
      have ht : t = t / gs * gs + t % gs := by rw [Nat.mul_comm]; exact (Nat.div_add_mod t gs).symm
      have hi : t / gs < N := by
        rw [hsn] at h1
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h1)
      have hk' : t % gs < gs := Nat.mod_lt _ hgs0
      have e1 := hnx (t / gs) hi (t % gs) hk'
      rw [← ht] at e1
      obtain ⟨hj, hje⟩ := hprod (t / gs) hi (t % gs) hk'
      rw [← ht] at hj hje
      rw [← getElem!_pos _ t h1, ← getElem!_pos _ t h2, e1, ← hje,
        Std.HashMap.getD_eq_getD_getElem?, hi1 _ hj, Option.getD_some]
    rw [hpar', hgen', hnxt']
  rw [closureSearch_eq_cs]
  refine hfin _ (forIn_range_break (fun q (s : CSt) => q ≤ N ∧ s.2.2.2.2 = q ∧
      RInv E par gen (cntC gs fn fp fl q) s.1 s.2.1 s.2.2.1 s.2.2.2.1)
    (fun s => RInv E par gen N s.1 s.2.1 s.2.2.1 s.2.2.2.1)
    (csOuter n gens) bound (csInit n) (fun q s hq hI => ?_) (fun s hI => ?_) ?_)
  · obtain ⟨E', par', gen', idx, head⟩ := s
    obtain ⟨hqN, hhead, hR⟩ := hI
    dsimp only at hhead hR
    subst hhead
    rcases Nat.lt_or_ge head N with hlt' | hge
    · obtain ⟨hqc, hc1⟩ := hrow head hlt'
      have hhs : head < E'.size := by rw [hR.1]; exact hqc
      have hx : E'[head]! = E[head]! := hR.2.1 head hqc
      have hinner : RInv E par gen (cK gs fn fp fl head (cntC gs fn fp fl head) gs)
          (forIn (m := Id) [:gens.size] (E', par', gen', idx) (csInner n gens head E'[head]!)).1
          (forIn (m := Id) [:gens.size] (E', par', gen', idx) (csInner n gens head E'[head]!)).2.1
          (forIn (m := Id) [:gens.size] (E', par', gen', idx) (csInner n gens head E'[head]!)).2.2.1
          (forIn (m := Id) [:gens.size] (E', par', gen', idx)
            (csInner n gens head E'[head]!)).2.2.2 := by
        refine forIn_range_yield (fun k (t : KSt) =>
            RInv E par gen (cK gs fn fp fl head (cntC gs fn fp fl head) k) t.1 t.2.1 t.2.2.1 t.2.2.2)
          (csInner n gens head E'[head]!) gens.size (E', par', gen', idx)
          (fun k t hk hJ => ?_) hR
        set c := cK gs fn fp fl head (cntC gs fn fp fl head) k with hc
        have hne := hKne head hlt' (k + 1) (by omega)
        have hle := hKle head hlt' (k + 1) (by omega)
        rw [cK_succ, ← hc] at hne hle ⊢
        obtain ⟨hj, hje⟩ := hprod head hlt' k hk
        rw [hn _ (hlt head hlt' k hk)] at hj hje
        rw [hx]
        rcases bfsHit_spec hne with ⟨h1, h2⟩ | ⟨h1, h3, h4, h2⟩
        ·
          have hfound : t.2.2.2.contains (compA n gens[k]! E[head]!) = true := by
            rw [Std.HashMap.contains_eq_isSome_getElem?, ← hje, hJ.2.2.1 _ h1]
            rfl
          refine ⟨t, ?_, ?_⟩
          · unfold csInner
            rw [hfound]
            rfl
          · rw [h2]
            exact hJ
        ·
          have hcN : c < N := by omega
          have hEc : E[c]! = compA n gens[k]! E[head]! := by rw [← h1]; exact hje
          have hnew : t.2.2.2.contains (compA n gens[k]! E[head]!) = false := by
            rw [Std.HashMap.contains_eq_isSome_getElem?]
            cases hz : t.2.2.2[compA n gens[k]! E[head]!]? with
            | none => rfl
            | some i =>
              obtain ⟨a, b⟩ := hJ.2.2.2.1 _ i hz
              rw [← hEc] at b
              have := hinj i (by omega) c hcN b
              omega
          have hR1 := rinv_new hJ hinj hcN ((hp c hcN).trans h3) ((hl c hcN).trans h4)
          rw [hEc] at hR1
          refine ⟨(t.1.push (compA n gens[k]! E[head]!), t.2.1.push head, t.2.2.1.push k,
            t.2.2.2.insert (compA n gens[k]! E[head]!) t.1.size), ?_, ?_⟩
          · unfold csInner
            rw [hnew]
            rfl
          · rw [h2]
            exact hR1
      refine ⟨fun b' hb' => ?_, fun b' hb' => ?_⟩
      · simp only [csOuter, hhs, ↓reduceIte] at hb'
        cases hb'
        refine ⟨by omega, rfl, ?_⟩
        dsimp only
        rw [hc1]
        exact hinner
      · simp only [csOuter, hhs, ↓reduceIte] at hb'
        cases hb'
    · have e : head = N := by omega
      subst e
      have hhs : ¬ N < E'.size := by rw [hR.1, hCN]; omega
      refine ⟨fun b' hb' => ?_, fun b' hb' => ?_⟩
      · simp only [csOuter, hhs, ↓reduceIte] at hb'
        cases hb'
      · simp only [csOuter, hhs, ↓reduceIte] at hb'
        cases hb'
        rw [hCN] at hR
        exact hR
  · obtain ⟨hqN, -, hR⟩ := hI
    have e : bound = N := by omega
    rw [e, hCN] at hR
    exact hR
  · have hc0 : cntC gs fn fp fl 0 = 1 := rfl
    refine ⟨Nat.zero_le _, rfl, ?_⟩
    rw [hc0]
    refine ⟨rfl, fun i hi => ?_, fun i hi => ?_, fun y i hy => ?_, rfl, fun i hi => ?_, rfl,
      fun i hi => ?_⟩
    all_goals dsimp only [csInit] at *
    · have hi0 : i = 0 := by omega
      subst hi0
      simp [hE0]
    · have hi0 : i = 0 := by omega
      subst hi0
      rw [hE0]
      simp
    · rw [Std.HashMap.getElem?_insert] at hy
      split_ifs at hy with hz
      · simp only [Option.some.injEq] at hy
        subst hy
        exact ⟨by omega, by rw [hE0]; exact beq_iff_eq.1 hz⟩
      · simp at hy
    · have hi0 : i = 0 := by omega
      subst hi0
      simp [hp 0 hpos, hp0]
    · have hi0 : i = 0 := by omega
      subst hi0
      simp [hl 0 hpos, hl0]

end CFSG.Sporadic.FischerOddCore.SearchSpec

end
