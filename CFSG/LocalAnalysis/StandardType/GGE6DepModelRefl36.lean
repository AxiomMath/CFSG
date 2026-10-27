module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeDefs

public section

namespace CFSG.StandardType

namespace E6Dep

private def refl36Words : List (List (Fin 6)) :=
  [[], [2], [1, 2], [3, 2], [5, 2], [0, 1, 2], [3, 1, 2], [4, 3, 2], [5, 1, 2], [5, 3, 2],
   [2, 3, 1, 2], [2, 5, 1, 2], [2, 5, 3, 2], [3, 0, 1, 2], [4, 3, 1, 2], [5, 0, 1, 2],
   [5, 3, 1, 2], [5, 4, 3, 2], [2, 3, 0, 1, 2], [2, 5, 0, 1, 2], [2, 5, 4, 3, 2],
   [4, 2, 3, 1, 2], [4, 3, 0, 1, 2], [5, 3, 0, 1, 2], [5, 4, 3, 1, 2], [1, 2, 3, 0, 1, 2],
   [1, 2, 5, 0, 1, 2], [3, 2, 5, 4, 3, 2], [3, 4, 2, 3, 1, 2], [4, 2, 3, 0, 1, 2],
   [5, 4, 3, 0, 1, 2], [3, 4, 2, 3, 0, 1, 2], [4, 1, 2, 3, 0, 1, 2], [3, 4, 1, 2, 3, 0, 1, 2],
   [2, 3, 4, 1, 2, 3, 0, 1, 2], [5, 2, 3, 4, 1, 2, 3, 0, 1, 2]]

private def reflWords : List Mat6 :=
  refl36Words.map fun w => evalWord gensL (w ++ 5 :: w.reverse)

private lemma evalWord_append {n : ℕ} (g : Fin n → Mat6) (l₁ l₂ : List (Fin n)) :
    evalWord g (l₁ ++ l₂) = evalWord g l₁ * evalWord g l₂ := by
  induction l₁ with
  | nil => simp [evalWord]
  | cons i l ih =>
      simp only [List.cons_append, evalWord, ih, mul_assoc]

private lemma evalWord_singleton (i : Fin 6) : evalWord gensL [i] = gensL i := by
  simp [evalWord]

private lemma evalWord_mem_closureL (l : List (Fin 6)) : evalWord gensL l ∈ closureL := by
  induction l with
  | nil => exact Submonoid.one_mem _
  | cons i l ih =>
      have hi : gensL i ∈ closureL :=
        Submonoid.subset_closure (show gensL i ∈ Set.range gensL from ⟨i, rfl⟩)
      exact Submonoid.mul_mem closureL hi ih

private lemma gensL_mul_self : ∀ i : Fin 6, gensL i * gensL i = 1 := by
  decide +kernel

private lemma gensL_mem_refl36 : ∀ i : Fin 6, gensL i ∈ refl36 := by
  decide +kernel

private lemma evalWord_reverse_both (l : List (Fin 6)) :
    evalWord gensL l * evalWord gensL l.reverse = 1 ∧
      evalWord gensL l.reverse * evalWord gensL l = 1 := by
  induction l with
  | nil => simp [evalWord]
  | cons i l ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · calc
          evalWord gensL (i :: l) * evalWord gensL (i :: l).reverse
              = (gensL i * evalWord gensL l) * (evalWord gensL l.reverse * gensL i) := by
                  rw [List.reverse_cons, evalWord_append, evalWord_singleton]
                  rw [show evalWord gensL (i :: l) = gensL i * evalWord gensL l from rfl]
          _ = gensL i * (evalWord gensL l * evalWord gensL l.reverse) * gensL i := by
                  ac_rfl
          _ = 1 := by
                  rw [h1, mul_one, gensL_mul_self i]
      · calc
          evalWord gensL (i :: l).reverse * evalWord gensL (i :: l)
              = (evalWord gensL l.reverse * gensL i) * (gensL i * evalWord gensL l) := by
                  rw [List.reverse_cons, evalWord_append, evalWord_singleton]
                  rw [show evalWord gensL (i :: l) = gensL i * evalWord gensL l from rfl]
          _ = evalWord gensL l.reverse * (gensL i * gensL i) * evalWord gensL l := by
                  ac_rfl
          _ = 1 := by
                  rw [gensL_mul_self i, mul_one, h2]

private lemma evalWord_reverse_mul_self (l : List (Fin 6)) :
    evalWord gensL l * evalWord gensL l.reverse = 1 :=
  (evalWord_reverse_both l).1

private lemma evalWord_reverse_mul (l : List (Fin 6)) :
    evalWord gensL l.reverse * evalWord gensL l = 1 :=
  (evalWord_reverse_both l).2

private lemma refl36_eq_reflWords : refl36 = reflWords.toFinset := by
  decide +kernel

private lemma mem_refl36_words {t : Mat6} (ht : t ∈ refl36) :
    ∃ w ∈ refl36Words, t = evalWord gensL (w ++ 5 :: w.reverse) := by
  have ht' : t ∈ reflWords.toFinset := by
    rw [← refl36_eq_reflWords]
    exact ht
  obtain ⟨w, hw, hwt⟩ := List.mem_map.mp (List.mem_toFinset.mp ht')
  exact ⟨w, hw, hwt.symm⟩

private lemma refl36_mul_self_aux :
    reflWords.all (fun a => decide (a * a = 1)) = true := by
  decide +kernel

private lemma gensL_conj_refl_aux :
    (List.finRange 6).all
        (fun i => reflWords.all (fun b => decide (gensL i * b * gensL i ∈ reflWords))) =
      true := by
  decide +kernel

private lemma refl36_mul_self_private {a : Mat6} (ha : a ∈ refl36) : a * a = 1 := by
  have ha' : a ∈ reflWords := by
    have : a ∈ reflWords.toFinset := by
      rw [← refl36_eq_reflWords]
      exact ha
    exact List.mem_toFinset.mp this
  exact of_decide_eq_true ((List.all_eq_true.mp refl36_mul_self_aux) a ha')

private lemma cancel_middle {A B C D : Mat6} (h : B * C = 1) :
    (A * B) * (C * D) = A * D := by
  have h' : (A * B) * (C * D) = A * (B * C) * D := by
    ac_rfl
  rw [h', h, mul_one]

private lemma conj_sandwich {A B C X D : Mat6} (hBC : B * C = 1) :
    (A * B) * (C * (X * B)) * (C * D) = A * X * D := by
  have h1 : (A * B) * (C * (X * B)) = A * (X * B) := by
    have h : (A * B) * (C * (X * B)) = A * (B * C) * (X * B) := by
      ac_rfl
    rw [h, hBC, mul_one]
  rw [h1]
  have h2 : (X * B) * (C * D) = X * D := by
    have h : (X * B) * (C * D) = X * (B * C) * D := by
      ac_rfl
    rw [h, hBC, mul_one]
  have h3 : (A * (X * B)) * (C * D) = A * ((X * B) * (C * D)) := by
    rw [mul_assoc]
  rw [h3, h2, mul_assoc]

private lemma closure_normalizes {T S : Finset Mat6} (hT : T ⊆ refl36) (hTS : T ⊆ S)
    (hS_conj : ConjClosed S) :
    ∀ g ∈ Submonoid.closure (T : Set Mat6), ∃ g' : Mat6,
      g * g' = 1 ∧ g' * g = 1 ∧ ∀ s ∈ S, g * s * g' ∈ S := by
  intro g hg
  induction hg using Submonoid.closure_induction with
  | mem x hxT =>
      refine ⟨x, refl36_mul_self_private (hT hxT), refl36_mul_self_private (hT hxT), ?_⟩
      intro s hs
      exact hS_conj x (hTS hxT) s hs
  | one =>
      refine ⟨1, by simp, by simp, ?_⟩
      intro s hs
      simpa using hs
  | mul x y hx hy ihx ihy =>
      obtain ⟨x', hx1, hx2, hxS⟩ := ihx
      obtain ⟨y', hy1, hy2, hyS⟩ := ihy
      refine ⟨y' * x', ?_, ?_, ?_⟩
      · rw [cancel_middle hy1, hx1]
      · rw [cancel_middle hx2, hy2]
      · intro s hs
        have heq : (x * y) * s * (y' * x') = x * (y * s * y') * x' := by
          ac_rfl
        rw [heq]
        exact hxS (y * s * y') (hyS s hs)

theorem refl36_subset_closureL : ∀ t ∈ refl36, t ∈ closureL := by
  intro t ht
  obtain ⟨w, _hw, rfl⟩ := mem_refl36_words ht
  exact evalWord_mem_closureL _

private lemma gensL_conj_refl_mem {i : Fin 6} {b : Mat6} (hb : b ∈ refl36) :
    gensL i * b * gensL i ∈ refl36 := by
  have hi : i ∈ List.finRange 6 := by simp
  have hb' : b ∈ reflWords := by
    have : b ∈ reflWords.toFinset := by
      rw [← refl36_eq_reflWords]
      exact hb
    exact List.mem_toFinset.mp this
  have h1 := (List.all_eq_true.mp gensL_conj_refl_aux) i hi
  have h2 := (List.all_eq_true.mp h1) b hb'
  have hmem : gensL i * b * gensL i ∈ reflWords := of_decide_eq_true h2
  rw [refl36_eq_reflWords]
  exact List.mem_toFinset.mpr hmem

private lemma closureL_conj_refl_both :
    ∀ a ∈ closureL, ∃ a' : Mat6,
      a * a' = 1 ∧ a' * a = 1 ∧ ∀ b ∈ refl36, a * b * a' ∈ refl36 := by
  intro a ha
  induction ha using Submonoid.closure_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      refine ⟨gensL i, gensL_mul_self i, gensL_mul_self i, ?_⟩
      intro b hb
      exact gensL_conj_refl_mem hb
  | one =>
      refine ⟨1, by simp, by simp, ?_⟩
      intro b hb
      simpa using hb
  | mul x y hx hy ihx ihy =>
      obtain ⟨x', hx1, hx2, hxS⟩ := ihx
      obtain ⟨y', hy1, hy2, hyS⟩ := ihy
      refine ⟨y' * x', ?_, ?_, ?_⟩
      · rw [cancel_middle hy1, hx1]
      · rw [cancel_middle hx2, hy2]
      · intro b hb
        have heq : (x * y) * b * (y' * x') = x * (y * b * y') * x' := by
          ac_rfl
        rw [heq]
        exact hxS (y * b * y') (hyS b hb)

private lemma refl36_conj_mem_private {a b : Mat6} (ha : a ∈ refl36) (hb : b ∈ refl36) :
    a * b * a ∈ refl36 := by
  have hac : a ∈ closureL := refl36_subset_closureL a ha
  obtain ⟨a', haa', _ha'a, hconj⟩ := closureL_conj_refl_both a hac
  have ha'eq : a' = a := by
    calc
      a' = (a * a) * a' := by rw [refl36_mul_self_private ha, one_mul]
      _ = a * (a * a') := by rw [mul_assoc]
      _ = a * 1 := by rw [haa']
      _ = a := by rw [mul_one]
  simpa [ha'eq] using hconj b hb

theorem closure_refl36 : Submonoid.closure (refl36 : Set Mat6) = closureL := by
  apply le_antisymm
  · rw [Submonoid.closure_le]
    intro t ht
    exact refl36_subset_closureL t ht
  · rw [closureL, Submonoid.closure_le]
    rintro g ⟨i, rfl⟩
    exact Submonoid.subset_closure (gensL_mem_refl36 i)

private lemma refl36_transitive_aux {s t : Mat6} (hs : s ∈ refl36) (ht : t ∈ refl36) :
    ∃ g ∈ closureL, ∃ g' ∈ closureL,
      g * g' = 1 ∧ g' * g = 1 ∧ g * s * g' = t := by
  obtain ⟨w₁, _hw₁, rfl⟩ := mem_refl36_words hs
  obtain ⟨w₂, _hw₂, rfl⟩ := mem_refl36_words ht
  refine ⟨evalWord gensL (w₂ ++ w₁.reverse), evalWord_mem_closureL _,
    evalWord gensL (w₁ ++ w₂.reverse), evalWord_mem_closureL _, ?_, ?_, ?_⟩
  · simp only [evalWord_append]
    rw [cancel_middle (evalWord_reverse_mul w₁)]
    exact evalWord_reverse_mul_self w₂
  · simp only [evalWord_append]
    rw [cancel_middle (evalWord_reverse_mul w₂)]
    exact evalWord_reverse_mul_self w₁
  · simp only [evalWord_append, evalWord]
    simpa only [mul_assoc] using
      conj_sandwich (A := evalWord gensL w₂) (B := evalWord gensL w₁.reverse)
        (C := evalWord gensL w₁) (X := gensL 5) (D := evalWord gensL w₂.reverse)
        (evalWord_reverse_mul w₁)

theorem closure_eq_closureL_iff {T : Finset Mat6} (hT : T ⊆ refl36) :
    Submonoid.closure (T : Set Mat6) = closureL ↔ ConjGenerates refl36 T := by
  classical
  constructor
  · intro hcl
    unfold ConjGenerates
    intro S hS_sub hS_conj hTS
    have hT_ne : T.Nonempty := by
      by_contra hT_not
      have hT_empty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT_not
      have hgens : gensL 0 ∈ Submonoid.closure (T : Set Mat6) := by
        rw [hcl]
        exact Submonoid.subset_closure ⟨0, rfl⟩
      rw [hT_empty] at hgens
      have h1 : gensL 0 = 1 := by
        simpa [Finset.coe_empty, Submonoid.closure_empty] using hgens
      have hne : gensL 0 ≠ 1 := by decide +kernel
      exact hne h1
    obtain ⟨s₀, hs₀T⟩ := hT_ne
    have hs₀S : s₀ ∈ S := hTS hs₀T
    have hs₀_refl : s₀ ∈ refl36 := hS_sub hs₀S
    have hrefl_subset : refl36 ⊆ S := by
      intro r hr
      obtain ⟨g, hg, g', _hg', hgg', _hg'g, hconj⟩ := refl36_transitive_aux hs₀_refl hr
      have hgT : g ∈ Submonoid.closure (T : Set Mat6) := by
        rw [hcl]
        exact hg
      obtain ⟨g'', _hgg'', hg''g, hnorm⟩ :=
        closure_normalizes hT hTS hS_conj g hgT
      have hg''eq : g'' = g' := by
        calc
          g'' = g'' * 1 := by rw [mul_one]
          _ = g'' * (g * g') := by rw [hgg']
          _ = (g'' * g) * g' := by rw [mul_assoc]
          _ = 1 * g' := by rw [hg''g]
          _ = g' := by rw [one_mul]
      have hmem : g * s₀ * g' ∈ S := by
        rw [← hg''eq]
        exact hnorm s₀ hs₀S
      rw [← hconj]
      exact hmem
    exact Finset.Subset.antisymm hS_sub hrefl_subset
  · intro hgen
    let S : Finset Mat6 := refl36.filter (fun a => a ∈ Submonoid.closure (T : Set Mat6))
    have hS_sub : S ⊆ refl36 := by
      intro a ha
      exact (Finset.mem_filter.mp ha).1
    have hS_conj : ConjClosed S := by
      intro a ha b hb
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr
        ⟨refl36_conj_mem_private ha'.1 hb'.1,
          Submonoid.mul_mem (Submonoid.closure (T : Set Mat6))
            (Submonoid.mul_mem (Submonoid.closure (T : Set Mat6)) ha'.2 hb'.2) ha'.2⟩
    have hTS : T ⊆ S := by
      intro t ht
      exact Finset.mem_filter.mpr ⟨hT ht, Submonoid.subset_closure ht⟩
    have hS_eq : S = refl36 := hgen S hS_sub hS_conj hTS
    have hsub : (refl36 : Set Mat6) ⊆ (Submonoid.closure (T : Set Mat6) : Set Mat6) := by
      intro a ha
      have haS : a ∈ S := by
        rw [hS_eq]
        exact ha
      exact (Finset.mem_filter.mp haS).2
    apply le_antisymm
    · rw [Submonoid.closure_le]
      intro t ht
      exact refl36_subset_closureL t (hT ht)
    · rw [← closure_refl36, Submonoid.closure_le]
      exact hsub

theorem refl36_mul_self {a : Mat6} (ha : a ∈ refl36) : a * a = 1 :=
  refl36_mul_self_private ha

theorem refl36_conj_mem {a b : Mat6} (ha : a ∈ refl36) (hb : b ∈ refl36) : a * b * a ∈ refl36 :=
  refl36_conj_mem_private ha hb

end E6Dep

end CFSG.StandardType

end
