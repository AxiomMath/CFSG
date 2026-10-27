module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary

private lemma cenM_countP_range_getD (l : List ℕ) :
    (List.range l.length).countP (fun i => decide (0 < l.getD i 0)) =
      l.countP (fun x => decide (0 < x)) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
        List.countP_cons]
      have hcomp : ((fun j => decide (0 < (a :: t).getD j 0)) ∘ Nat.succ) =
          fun i => decide (0 < t.getD i 0) := by
        funext i
        simp [Function.comp_apply]
      rw [hcomp, ih]
      simp

private lemma cenM_countP_pos_eq_length_filter (l : List ℕ) :
    l.countP (fun x => decide (0 < x)) = (l.filter (fun x => decide (x ≠ 0))).length := by
  rw [List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro x _
  rw [decide_eq_decide]
  exact Nat.pos_iff_ne_zero

private lemma cenM_countP_range_eq_headD_add_tail (m : List ℕ) :
    (List.range m.length).countP (fun j => decide (0 < m.getD j 0)) =
      (if 0 < m.headD 0 then 1 else 0) + m.tail.countP (fun x => decide (0 < x)) := by
  cases m with
  | nil => rfl
  | cons a t =>
      rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map]
      have hcomp : ((fun j => decide (0 < (a :: t).getD j 0)) ∘ Nat.succ) =
          fun i => decide (0 < t.getD i 0) := by
        funext i
        simp [Function.comp_apply]
      rw [hcomp, cenM_countP_range_getD t]
      simp
      omega

private lemma cenM_countP_map_succ_range (m : List ℕ) (h : ℕ) :
    (List.range h).countP (fun i => decide (0 < m.getD (i + 1) 0)) =
      (List.range (h + 1)).countP (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) := by
  rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
  have h0 : (if decide (1 ≤ 0 ∧ 0 < m.getD 0 0) = true then 1 else 0) = 0 := by simp
  rw [h0, Nat.add_zero]
  apply List.countP_congr
  intro i _
  simp [Function.comp_apply]

private lemma cenM_countP_range_reflect (n : ℕ) : ∀ f : ℕ → Bool,
    (List.range n).countP (fun i => f (n - i)) =
      (List.range n).countP (fun i => f (i + 1)) := by
  induction n with
  | zero => intro f; rfl
  | succ n ih =>
      intro f
      have hL : (List.range (n + 1)).countP (fun i => f ((n + 1) - i)) =
          (List.range n).countP (fun i => f (n - i)) + (if f (n + 1) then 1 else 0) := by
        rw [List.range_succ_eq_map, List.countP_cons, List.countP_map, Nat.add_zero]
        congr 1
        apply List.countP_congr
        intro i _
        simp only [Function.comp_apply, Nat.succ_eq_add_one]
        rw [show n + 1 - (i + 1) = n - i by omega]
      have hR : (List.range (n + 1)).countP (fun i => f (i + 1)) =
          (List.range n).countP (fun i => f (i + 1)) + (if f (n + 1) then 1 else 0) := by
        rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil, Nat.zero_add]
      rw [hL, ih f, hR]

private lemma cenM_tail_countP_eq_range {m : List ℕ} {p : ℕ} (hp : 1 ≤ p) (hlen : m.length = p) :
    m.tail.countP (fun x => decide (0 < x)) =
      (List.range p).countP (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) := by
  rw [← cenM_countP_range_getD m.tail]
  have h1 : (List.range m.tail.length).countP (fun i => decide (0 < m.tail.getD i 0)) =
      (List.range (p - 1)).countP (fun i => decide (0 < m.getD (i + 1) 0)) := by
    rw [List.length_tail, hlen]
    apply List.countP_congr
    intro i _
    cases m with
    | nil => simp
    | cons a t => simp
  rw [h1, cenM_countP_map_succ_range]
  rw [show p - 1 + 1 = p by omega]

private lemma cenM_two_mul_countP_of_symm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : List ℕ}
    (hlen : m.length = p)
    (hsymm : ∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0) :
    2 * ((List.range ((p - 1) / 2 + 1)).countP
        (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))) =
      m.tail.countP (fun x => decide (0 < x)) := by
  classical
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpH : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have hk' : (p - 1) / 2 = k := by omega
    omega
  have hhalf : (p - 1) / 2 + 1 + ((p - 1) / 2) = p := by omega
  rw [cenM_tail_countP_eq_range hp1 hlen]
  rw [show List.range p = List.range ((p - 1) / 2 + 1) ++
      (List.range ((p - 1) / 2)).map (fun x => ((p - 1) / 2 + 1) + x) from by
    rw [← List.range_add, hhalf]]
  rw [List.countP_append, List.countP_map]
  have hfirst : (List.range ((p - 1) / 2 + 1)).countP
        (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) =
      (List.range ((p - 1) / 2)).countP (fun i => decide (0 < m.getD (i + 1) 0)) := by
    rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
    have h0 : (if decide (1 ≤ 0 ∧ 0 < m.getD 0 0) = true then 1 else 0) = 0 := by simp
    rw [h0, Nat.add_zero]
    apply List.countP_congr
    intro i _
    simp [Function.comp_apply]
  have hsnd : (List.range ((p - 1) / 2)).countP
        ((fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) ∘
          fun x => ((p - 1) / 2 + 1) + x) =
      (List.range ((p - 1) / 2)).countP (fun i => decide (0 < m.getD (i + 1) 0)) := by
    rw [show (List.range ((p - 1) / 2)).countP
          ((fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) ∘
            fun x => ((p - 1) / 2 + 1) + x) =
        (List.range ((p - 1) / 2)).countP
          (fun i => decide (0 < m.getD ((p - 1) / 2 - i) 0)) from by
      apply List.countP_congr
      intro i hi
      rw [List.mem_range] at hi
      rw [Function.comp_apply, decide_eq_true_eq, decide_eq_true_eq]
      have hlt : ((p - 1) / 2 + 1) + i < p := by omega
      have hmod : (p - (((p - 1) / 2 + 1) + i)) % p = (p - 1) / 2 - i := by
        rw [Nat.mod_eq_of_lt] <;> omega
      have key : m.getD (((p - 1) / 2 + 1) + i) 0 = m.getD ((p - 1) / 2 - i) 0 := by
        rw [← hsymm _ hlt, hmod]
      have h1 : 1 ≤ ((p - 1) / 2 + 1) + i := by omega
      rw [key]
      exact ⟨fun h => h.2, fun h => ⟨h1, h⟩⟩]
    exact cenM_countP_range_reflect ((p - 1) / 2) (fun x => decide (0 < m.getD x 0))
  rw [hfirst, hsnd]
  omega

private lemma cenM_countP_pos_le_sum (l : List ℕ) :
    l.countP (fun x => decide (0 < x)) ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.countP_cons, List.sum_cons]
      by_cases ha : 0 < a
      · have hdec : decide (0 < a) = true := by simpa using ha
        rw [if_pos hdec]
        omega
      · have hdec : decide (0 < a) = false := by simp [ha]
        rw [if_neg (by simp [hdec])]
        omega

private lemma cenM_tail_sum_le (m : List ℕ) : m.tail.sum ≤ m.sum := by
  cases m with
  | nil => simp
  | cons a t => simp

private lemma cenM_three_le_of_two_le_countP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {m : List ℕ} {N : ℕ} (hlen : m.length = p) (hsum : m.sum = N)
    (hsymm : ∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0)
    (h2 : 2 ≤ (List.range ((p - 1) / 2 + 1)).countP
      (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))) :
    3 ≤ N := by
  have hdbl := cenM_two_mul_countP_of_symm hp hp2 hlen hsymm
  have hle : m.tail.countP (fun x => decide (0 < x)) ≤ m.tail.sum :=
    cenM_countP_pos_le_sum m.tail
  have hle' : m.tail.sum ≤ m.sum := cenM_tail_sum_le m
  omega

private lemma cenM_three_le_of_two_le_filter {p : ℕ} {m : List ℕ} {N : ℕ}
    (hlen : m.length = p) (hsum : m.sum = N)
    (h2 : 2 ≤ ((List.range p).filter (fun j => decide (0 < m.getD j 0))).length - 1) :
    3 ≤ N := by
  have hs : ((List.range p).filter (fun j => decide (0 < m.getD j 0))).length =
      m.countP (fun x => decide (0 < x)) := by
    rw [← List.countP_eq_length_filter, ← hlen, cenM_countP_range_getD]
  have hle : m.countP (fun x => decide (0 < x)) ≤ m.sum := cenM_countP_pos_le_sum m
  omega

private lemma cenM_rZ_trivial (p nf d : ℕ) (tw : Bool) (m : List ℕ)
    (h : (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)) :
    (ggMultDatumA p nf d tw m).rZ =
      ((List.range p).filter (fun j => decide (0 < m.getD j 0))).length - 1 := by
  unfold ggMultDatumA
  rw [if_pos h]

private lemma cenM_rZ_nontrivial (p nf d : ℕ) (tw : Bool) (m : List ℕ)
    (h : ¬ ((tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2))) :
    (ggMultDatumA p nf d tw m).rZ =
      ((List.range ((p - 1) / 2 + 1)).filter
        (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).length := by
  unfold ggMultDatumA
  rw [if_neg h]

private lemma cenM_pos_headD_iff_mem_primaryFactors {N : ℕ} {K : Type} [Field K]
    {x : GL (Fin N) K} {m : List ℕ}
    (hsq : Squarefree (minpoly K (ggK1A_glEnd x)))
    (hhead : m.getD 0 0 = Module.finrank K
      (primaryComponent (ggK1A_glEnd x) (X - 1))) :
    0 < m.headD 0 ↔ X - 1 ∈ primaryFactors (ggK1A_glEnd x) := by
  have hheadD : m.headD 0 = m.getD 0 0 := by
    cases m with
    | nil => rfl
    | cons a t => rfl
  have h1 : 0 < m.headD 0 ↔
      0 < Module.finrank K (primaryComponent (ggK1A_glEnd x) (X - 1)) := by
    rw [hheadD, hhead]
  rw [h1]
  constructor
  · intro hpos
    have hne : primaryComponent (ggK1A_glEnd x) (X - 1) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hpos
      simp at hpos
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hxv : ggK1A_glEnd x v = v := by
      have h0 := hv
      rw [primaryComponent, LinearMap.mem_ker, map_sub, aeval_X, map_one] at h0
      simpa [sub_eq_zero] using h0
    have hmem : v ∈ (ggK1A_glEnd x).eigenspace 1 := by
      rw [Module.End.mem_eigenspace_iff]
      simpa using hxv
    have hev : (ggK1A_glEnd x).HasEigenvalue 1 := by
      rw [Module.End.hasEigenvalue_iff]
      intro hbot
      rw [hbot] at hmem
      exact hv0 (by simpa using hmem)
    have hroot : (minpoly K (ggK1A_glEnd x)).IsRoot 1 :=
      (Module.End.hasEigenvalue_iff_isRoot).mp hev
    rw [mem_primaryFactors]
    refine ⟨?_, ?_, ?_⟩
    · simpa using irreducible_X_sub_C (1 : K)
    · simpa using monic_X_sub_C (1 : K)
    · rw [show (X - 1 : K[X]) = X - C 1 from by simp]
      exact dvd_iff_isRoot.mpr hroot
  · intro hmem
    have : Nontrivial ↥(primaryComponent (ggK1A_glEnd x) (X - 1)) :=
      Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hmem)
    exact Module.finrank_pos

private lemma cenM_selfDual_card_of_mem {N : ℕ} {K : Type} [Field K] {x : GL (Fin N) K}
    (h : X - 1 ∈ primaryFactors (ggK1A_glEnd x)) :
    (ggK1A_selfDualFactors x).card + 1 = (primaryFactors (ggK1A_glEnd x)).card := by
  classical
  have hunfold : ggK1A_selfDualFactors x =
      (primaryFactors (ggK1A_glEnd x)).erase (X - 1) := by
    unfold ggK1A_selfDualFactors
    exact Finset.filter_ne' _ _
  rw [hunfold, Finset.card_erase_add_one h]

private lemma cenM_selfDual_card_of_not_mem {N : ℕ} {K : Type} [Field K] {x : GL (Fin N) K}
    (h : X - 1 ∉ primaryFactors (ggK1A_glEnd x)) :
    (ggK1A_selfDualFactors x).card = (primaryFactors (ggK1A_glEnd x)).card := by
  classical
  have hunfold : ggK1A_selfDualFactors x =
      (primaryFactors (ggK1A_glEnd x)).erase (X - 1) := by
    unfold ggK1A_selfDualFactors
    exact Finset.filter_ne' _ _
  rw [hunfold, Finset.erase_eq_of_notMem h]

theorem ggK1A_rZ_eq_card_primaryFactors_sub_one {p nf N d : ℕ} {tw : Bool} {K : Type}
    [Field K] {x : GL (Fin N) K} {m : List ℕ}
    (hsq : Squarefree (minpoly K (ggK1A_glEnd x)))
    (htriv : (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)) (hd : d = ggMultOrd p nf)
    (hm : GGK1AMultOf p nf N tw K x m) :
    (ggMultDatumA p nf d tw m).rZ = (primaryFactors (ggK1A_glEnd x)).card - 1 := by
  classical
  have hnot : ¬ (ggMultOrd p nf = 2 ∧ tw = false) := by
    rintro ⟨h2, hf⟩
    rcases htriv with ⟨-, hd1⟩ | ⟨ht, -⟩
    · omega
    · rw [ht] at hf
      exact Bool.noConfusion hf
  obtain ⟨-, -, hmult⟩ := hm.blocks_eq.resolve_left (fun h => hnot h.1)
  have hmcard : (m.tail.filter (fun j => decide (j ≠ 0))).length =
      (ggK1A_selfDualFactors x).card := by
    have h := congrArg Multiset.card hmult
    rw [Multiset.coe_card, Multiset.card_map] at h
    simpa using h
  rw [cenM_rZ_trivial p nf d tw m htriv]
  have hs : ((List.range p).filter (fun j => decide (0 < m.getD j 0))).length =
      (if 0 < m.headD 0 then 1 else 0) + (ggK1A_selfDualFactors x).card := by
    rw [← List.countP_eq_length_filter, ← hm.length_eq, cenM_countP_range_eq_headD_add_tail,
      cenM_countP_pos_eq_length_filter, hmcard]
  have hif : (if 0 < m.headD 0 then 1 else 0) =
      (if X - 1 ∈ primaryFactors (ggK1A_glEnd x) then 1 else 0) := by
    have hiff := cenM_pos_headD_iff_mem_primaryFactors hsq hm.head_eq
    by_cases h : 0 < m.headD 0
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  have hS : (ggK1A_selfDualFactors x).card +
      (if X - 1 ∈ primaryFactors (ggK1A_glEnd x) then 1 else 0) =
      (primaryFactors (ggK1A_glEnd x)).card := by
    by_cases hb : X - 1 ∈ primaryFactors (ggK1A_glEnd x)
    · rw [if_pos hb]
      exact cenM_selfDual_card_of_mem hb
    · rw [if_neg hb, Nat.add_zero]
      exact cenM_selfDual_card_of_not_mem hb
  omega

theorem ggK1A_rZ_eq_card_selfDualFactors {p nf N d : ℕ} {K : Type} [Field K]
    {x : GL (Fin N) K} {m : List ℕ} (hd : d = ggMultOrd p nf) (hord : ggMultOrd p nf = 2)
    (hm : GGK1AMultOf p nf N false K x m) :
    (ggMultDatumA p nf d false m).rZ = (ggK1A_selfDualFactors x).card := by
  classical
  have htriv : ¬ ((false = false ∧ d = 1) ∨ (false = true ∧ d = 2)) := by
    rintro (⟨-, h1⟩ | ⟨h2, -⟩)
    · omega
    · exact Bool.noConfusion h2
  obtain ⟨-, -, hmult⟩ := hm.blocks_eq.resolve_right (fun h => h.1 ⟨hord, rfl⟩)
  have hmcard : (((List.range ((p - 1) / 2)).map (fun j => m.getD (j + 1) 0)).filter
      (fun j => decide (j ≠ 0))).length = (ggK1A_selfDualFactors x).card := by
    have h := congrArg Multiset.card hmult
    rw [Multiset.coe_card, Multiset.card_map] at h
    simpa using h
  rw [cenM_rZ_nontrivial p nf d false m htriv, ← hmcard]
  rw [← cenM_countP_pos_eq_length_filter, ← List.countP_eq_length_filter, List.countP_map]
  rw [show ((fun x => decide (0 < x)) ∘ (fun j => m.getD (j + 1) 0)) =
      (fun j => decide (0 < m.getD (j + 1) 0)) from rfl]
  rw [cenM_countP_map_succ_range]

theorem ggK1A_uni_two_mul_rZ_eq_card_selfDualFactors {p nf N d : ℕ} {K : Type} [Field K]
    {x : GL (Fin N) K} {m : List ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : d = ggMultOrd p nf)
    (hord : ggMultOrd p nf = 1) (hm : GGK1AMultOf p nf N true K x m) :
    2 * (ggMultDatumA p nf d true m).rZ = (ggK1A_selfDualFactors x).card := by
  classical
  have htriv : ¬ ((true = false ∧ d = 1) ∨ (true = true ∧ d = 2)) := by
    rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · exact Bool.noConfusion h1
    · omega
  obtain ⟨-, himp, hmult⟩ := hm.blocks_eq.resolve_left (fun h => by
    have h2 : ggMultOrd p nf = 2 := h.1.1
    omega)
  have hsymm := himp ⟨hord, rfl⟩
  have hmcard : (m.tail.filter (fun j => decide (j ≠ 0))).length =
      (ggK1A_selfDualFactors x).card := by
    have h := congrArg Multiset.card hmult
    rw [Multiset.coe_card, Multiset.card_map] at h
    simpa using h
  rw [cenM_rZ_nontrivial p nf d true m htriv, ← hmcard]
  rw [← cenM_countP_pos_eq_length_filter, ← List.countP_eq_length_filter]
  exact cenM_two_mul_countP_of_symm hp hp2 hm.length_eq hsymm

private lemma cenM_ggMultOrd_eq_one_or_two {p nf : ℕ}
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) : ggMultOrd p nf = 1 ∨ ggMultOrd p nf = 2 := by
  rcases hdvd with h | h
  · left
    unfold ggMultOrd
    rw [if_pos h]
  · unfold ggMultOrd
    split_ifs with h1
    · left
      rfl
    · right
      rfl

theorem ggK1A_three_le_of_two_le_rZ {p nf N d : ℕ} {tw : Bool} {K : Type} [Field K]
    {x : GL (Fin N) K} {m : List ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hd : d = ggMultOrd p nf)
    (hm : GGK1AMultOf p nf N tw K x m) (h2 : 2 ≤ (ggMultDatumA p nf d tw m).rZ) : 3 ≤ N := by
  classical
  have hsum : m.sum = N := hm.sum_eq
  rcases cenM_ggMultOrd_eq_one_or_two hdvd with hord | hord
  · rcases tw with _ | _
    ·
      have htriv : ((false = false ∧ d = 1) ∨ (false = true ∧ d = 2)) :=
        Or.inl ⟨rfl, by omega⟩
      rw [cenM_rZ_trivial p nf d false m htriv] at h2
      exact cenM_three_le_of_two_le_filter hm.length_eq hsum h2
    ·
      have htriv : ¬ ((true = false ∧ d = 1) ∨ (true = true ∧ d = 2)) := by
        rintro (⟨h1, -⟩ | ⟨-, h2'⟩)
        · exact Bool.noConfusion h1
        · omega
      obtain ⟨-, himp, -⟩ := hm.blocks_eq.resolve_left (fun h => by
        have h2' : ggMultOrd p nf = 2 := h.1.1
        omega)
      have hsymm := himp ⟨hord, rfl⟩
      rw [cenM_rZ_nontrivial p nf d true m htriv] at h2
      have hcount : 2 ≤ (List.range ((p - 1) / 2 + 1)).countP
          (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) := by
        rw [List.countP_eq_length_filter]
        exact h2
      exact cenM_three_le_of_two_le_countP hp hp2 hm.length_eq hm.sum_eq hsymm hcount
  · rcases tw with _ | _
    ·
      have htriv : ¬ ((false = false ∧ d = 1) ∨ (false = true ∧ d = 2)) := by
        rintro (⟨-, h1⟩ | ⟨h2', -⟩)
        · omega
        · exact Bool.noConfusion h2'
      obtain ⟨-, hsymm, -⟩ := hm.blocks_eq.resolve_right (fun h => h.1 ⟨hord, rfl⟩)
      rw [cenM_rZ_nontrivial p nf d false m htriv] at h2
      have hcount : 2 ≤ (List.range ((p - 1) / 2 + 1)).countP
          (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) := by
        rw [List.countP_eq_length_filter]
        exact h2
      exact cenM_three_le_of_two_le_countP hp hp2 hm.length_eq hm.sum_eq hsymm hcount
    ·
      have htriv : ((true = false ∧ d = 1) ∨ (true = true ∧ d = 2)) :=
        Or.inr ⟨rfl, by omega⟩
      rw [cenM_rZ_trivial p nf d true m htriv] at h2
      exact cenM_three_le_of_two_le_filter hm.length_eq hsum h2

end CFSG.StandardType

end
