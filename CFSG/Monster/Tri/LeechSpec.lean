module

public import CFSG.Monster.Tri.LeechGraph
public import CFSG.Monster.Tri.LeechCheck

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.B.Short CFSG.Monster.B.Co2

theorem preconnected_induce_of_tree {V : Type*} (G : SimpleGraph V) (A : Set V) (pt : ℕ → V)
    (n : ℕ) (par lev : ℕ → ℕ) (hmem : ∀ i < n, pt i ∈ A)
    (hpar : ∀ i < n, i ≠ 0 → par i < n ∧ lev (par i) + 1 = lev i ∧ G.Adj (pt i) (pt (par i)))
    (hcov : ∀ a ∈ A, ∃ i < n, pt i = a) : (G.induce A).Preconnected := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨i, hi, rfl⟩ := hcov a ha
  obtain ⟨j, hj, rfl⟩ := hcov b hb
  have h0n : 0 < n := by omega
  have key : ∀ m, ∀ k (hk : k < n), lev k ≤ m →
      (G.induce A).Reachable ⟨pt 0, hmem 0 h0n⟩ ⟨pt k, hmem k hk⟩ := by
    intro m
    induction m with
    | zero =>
      intro k hk hl
      by_cases hk0 : k = 0
      · subst hk0
        exact SimpleGraph.Reachable.refl _
      · have := (hpar k hk hk0).2.1
        omega
    | succ m ih =>
      intro k hk hl
      by_cases hk0 : k = 0
      · subst hk0
        exact SimpleGraph.Reachable.refl _
      · obtain ⟨hp, hlev, hadj⟩ := hpar k hk hk0
        exact (ih (par k) hp (by omega)).trans
          (SimpleGraph.Adj.reachable (SimpleGraph.induce_adj.2 hadj.symm))
  exact (key _ i hi le_rfl).symm.trans (key _ j hj le_rfl)

theorem image_shortFound_eq :
    dec '' (shortFound Native.shortTables : Set ℕ) = shortSet := by
  have hsub := shortFacts.image_shortFound_subset_orbit kGenN_smul_dec
  rw [closure_kGenN_Iio, dec_shortSeed] at hsub
  have hcard := shortFacts.ncard_image_shortFound dec_inj
  exact Set.eq_of_subset_of_ncard_le (hsub.trans orbit_Kvis_short.le)
    (by rw [ncard_shortSet, hcard]; rfl)

theorem shortHit_klev_iff_mem (T : CFSG.Monster.B.Short.Native.ShortTables) {n : ℕ} :
    shortHit T.klev n = true ↔ n ∈ shortFound T := by
  simp only [shortHit, shortFound, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq, Finset.mem_filter, Finset.mem_range]

theorem shortHit_iff_mem {n : ℕ} :
    shortHit shortKlev n = true ↔ n ∈ shortFound Native.shortTables := by
  rw [shortKlev, tablesKlev]
  exact shortHit_klev_iff_mem _

theorem shortHit_iff
    {n : ℕ} : shortHit shortKlev n = true ↔ n < 2 ^ 24 ∧ dec n ∈ shortSet := by
  rw [shortHit_iff_mem]
  constructor
  · intro h
    refine ⟨Finset.mem_range.1 (Finset.mem_filter.1 h).1, ?_⟩
    rw [← image_shortFound_eq]
    exact ⟨n, h, rfl⟩
  · rintro ⟨hn, h⟩
    rw [← image_shortFound_eq] at h
    obtain ⟨m, hm, hmn⟩ := h
    have hm' := Finset.mem_range.1 (Finset.mem_filter.1 hm).1
    rw [dec_inj m n hm' hn hmn] at hm
    exact hm

theorem exists_shortHit_of_mem_shortSet
    {x : L2} (hx : x ∈ shortSet) :
    ∃ n, shortHit shortKlev n = true ∧ dec n = x := by
  rw [← image_shortFound_eq] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨n, shortHit_iff_mem.2 hn, rfl⟩

theorem dec_12288 : dec 12288 = v0 := vShort_eq_v0

theorem shortHit_xor_iff
    {m n : ℕ} (hm : m < 2 ^ 24) (hn : n < 2 ^ 24) :
    shortHit shortKlev (m ^^^ n) = true ↔ dec m + dec n ∈ shortSet := by
  rw [shortHit_iff, dec_xor]
  exact ⟨fun h => h.2, fun h => ⟨Nat.xor_lt_two_pow hm hn, h⟩⟩

theorem adj_dec_iff {m n : ℕ} (hm : shortHit shortKlev m = true)
    (hn : shortHit shortKlev n = true) :
    shortGraph.Adj (dec m) (dec n) ↔ shortHit shortKlev (m ^^^ n) = true := by
  obtain ⟨hm1, hm2⟩ := shortHit_iff.1 hm
  obtain ⟨hn1, hn2⟩ := shortHit_iff.1 hn
  rw [shortGraph_adj, shortHit_xor_iff hm1 hn1]
  exact ⟨fun h => h.2.2, fun h => ⟨hm2, hn2, h⟩⟩

theorem shortHit_12288 : shortHit shortKlev 12288 = true :=
  shortHit_iff.2 ⟨by norm_num, by rw [dec_12288]; exact classOf_vMinus_mem_shortSet⟩

theorem adj_v0_dec_iff {n : ℕ} (hn : shortHit shortKlev n = true) :
    shortGraph.Adj v0 (dec n) ↔ shortHit shortKlev (n ^^^ 12288) = true := by
  rw [← dec_12288, adj_dec_iff shortHit_12288 hn, Nat.xor_comm]

theorem leechCheck_parts :
    nbrOK shortKlev leechNbr = true ∧ treeOK shortKlev leechNbr leechNbrPar leechNbrLev = true ∧
    muOK shortKlev leechNbr 1 leechIdx3 = true ∧
    treeOK shortKlev leechIdx3 leechPar3 leechLev3 = true ∧
    muOK shortKlev leechNbr 64 leechIdx4 = true ∧
    treeOK shortKlev leechIdx4 leechPar4 leechLev4 = true ∧
    shortHit shortKlev (12288 ^^^ 64) = false := by
  have h := leechCheck_eq_true
  simp only [leechCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem not_mem_shortSet_v0_add_ell6 :
    v0 + dec 64 ∉ shortSet := by
  intro h
  have h7 := leechCheck_parts.2.2.2.2.2.2
  rw [← dec_12288, ← shortHit_xor_iff (by norm_num) (by norm_num)] at h
  rw [h] at h7
  exact absurd h7 (by decide)

theorem sortedOK_spec {vs : Array Nat} (h : sortedOK vs = true) :
    ∀ i j, i < j → j < vs.size → vs[i]! < vs[j]! := by
  simp only [sortedOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  have step : ∀ i, i + 1 < vs.size → vs[i]! < vs[i + 1]! := fun i hi =>
    (h i (by omega)).resolve_left (by omega)
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hij' : i < j
    · exact (ih hij' (by omega)).trans (step j hj)
    · obtain rfl : i = j := by omega
      exact step i hj

theorem mem_toList_iff {vs : Array Nat} {n : Nat} :
    n ∈ vs.toList ↔ ∃ i, i < vs.size ∧ vs[i]! = n := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
    have hi' : i < vs.size := by simpa using hi
    exact ⟨i, hi', by rw [getElem!_pos vs i hi']; exact (Array.getElem_toList hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by simpa using hi, by simp [hi]⟩

theorem nbrOK_spec {k : ByteArray} {nbr : Array Nat} (h : nbrOK k nbr = true) :
    nbr.size = 4600 ∧ (∀ i j, i < j → j < nbr.size → nbr[i]! < nbr[j]!) ∧
    (∀ i < nbr.size, shortHit k nbr[i]! = true ∧ shortHit k (nbr[i]! ^^^ 12288) = true) := by
  simp only [nbrOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hsz, hs⟩, hall⟩ := h
  exact ⟨hsz, sortedOK_spec hs, hall⟩

theorem treeOK_spec {k : ByteArray} {vs par lev : Array Nat} (h : treeOK k vs par lev = true) :
    ∀ i, i ≠ 0 → i < vs.size → par[i]! < vs.size ∧ lev[par[i]!]! + 1 = lev[i]! ∧
      shortHit k (vs[i]! ^^^ vs[par[i]!]!) = true := by
  simp only [treeOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  intro i hi0 hi
  rcases h i hi with h1 | ⟨⟨h2, h3⟩, h4⟩
  · exact absurd h1 hi0
  · exact ⟨h2, h3, h4⟩

theorem muOK_spec {k : ByteArray} {nbr : Array Nat} {b : Nat} {vs : Array Nat}
    (h : muOK k nbr b vs = true) :
    (∀ i j, i < j → j < vs.size → vs[i]! < vs[j]!) ∧
    (∀ i < vs.size, shortHit k vs[i]! = true ∧ shortHit k (vs[i]! ^^^ 12288) = true ∧
      shortHit k (vs[i]! ^^^ b) = true) ∧
    (∀ n ∈ nbr.toList, shortHit k (n ^^^ b) = true → n ∈ vs.toList) := by
  simp only [muOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h
  obtain ⟨⟨hs, hv⟩, hn⟩ := h
  refine ⟨sortedOK_spec hs, fun i hi => ?_, fun n hn' hb => ?_⟩
  · have := hv vs[i]! (mem_toList_iff.2 ⟨i, hi, rfl⟩)
    exact ⟨this.1.1, this.1.2, this.2⟩
  · rcases hn n hn' with h1 | h1
    · rw [h1] at hb
      exact absurd hb (by decide)
    · exact h1

end CFSG.Monster.Tri.Leech
