module

public import CFSG.Quasithin.Recognition.UniquenessSystemMoves

public section

namespace CFSG.Quasithin.Asc94

universe u

variable {V : Type u} {Δ : SimpleGraph V} {C : Set (List V)}

theorem exists_dup_split : ∀ {l : List V}, ¬ l.Nodup →
    ∃ (P : List V) (a : V) (Q R : List V), l = P ++ a :: (Q ++ a :: R)
  | [], h => absurd List.nodup_nil h
  | b :: l, h => by
    rw [List.nodup_cons, not_and_or, not_not] at h
    rcases h with h | h
    · obtain ⟨Q, R, rfl⟩ := List.mem_iff_append.mp h
      exact ⟨[], b, Q, R, rfl⟩
    · obtain ⟨P, a, Q, R, rfl⟩ := exists_dup_split h
      exact ⟨b :: P, a, Q, R, rfl⟩

theorem inClosure_of_mem {c : List V} (hc : IsCycle Δ c) (hC : c ∈ C) : InClosure Δ C c := by
  obtain ⟨a, s, rfl | rfl⟩ := hc.eq_cons
  · exact ⟨a, Relation.ReflTransGen.refl⟩
  · refine ⟨a, ?_⟩
    have := Moves.cycDel_mem (Γ := Δ) [] [] (a :: (s ++ [a])) hC rfl
      (by rw [← List.cons_append, List.getLast?_concat])
    simpa using this

theorem isNGon_three {a b c : V} (hab : Δ.Adj a b) (hbc : Δ.Adj b c) (hca : Δ.Adj c a) :
    IsNGon Δ 3 [a, b, c, a] := by
  refine ⟨⟨⟨List.cons_ne_nil _ _, ?_⟩, rfl⟩, rfl, ?_⟩
  · simp [List.isChain_cons_cons, hab, hbc, hca]
  · simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, List.nodup_nil, not_false_eq_true,
      and_true]
    exact ⟨not_or.mpr ⟨hab.ne, hca.ne.symm⟩, hbc.ne⟩

theorem isNGon_four {a b c d : V} (hab : Δ.Adj a b) (hbc : Δ.Adj b c) (hcd : Δ.Adj c d)
    (hda : Δ.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) : IsNGon Δ 4 [a, b, c, d, a] := by
  refine ⟨⟨⟨List.cons_ne_nil _ _, ?_⟩, rfl⟩, rfl, ?_⟩
  · simp [List.isChain_cons_cons, hab, hbc, hcd, hda]
  · simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, List.nodup_nil, not_false_eq_true,
      and_true]
    exact ⟨not_or.mpr ⟨hab.ne, not_or.mpr ⟨hac, hda.ne.symm⟩⟩, not_or.mpr ⟨hbc.ne, hbd⟩,
      hcd.ne⟩

theorem IsNGon.three {c : List V} (hc : IsNGon Δ 3 c) :
    ∃ u v w, c = [u, v, w, u] ∧ Δ.Adj u v ∧ Δ.Adj v w ∧ Δ.Adj w u := by
  obtain ⟨⟨⟨-, hch⟩, hhl⟩, hlen, -⟩ := hc
  match c, hlen with
  | [a, b, c', d], _ =>
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at hhl
    subst hhl
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact ⟨a, b, c', rfl, hch.1, hch.2.1, hch.2.2⟩

theorem IsNGon.four {c : List V} (hc : IsNGon Δ 4 c) :
    ∃ a b c' d, c = [a, b, c', d, a] ∧ Δ.Adj a b ∧ Δ.Adj b c' ∧ Δ.Adj c' d ∧ Δ.Adj d a ∧
      a ≠ c' ∧ b ≠ d := by
  obtain ⟨⟨⟨-, hch⟩, hhl⟩, hlen, hnd⟩ := hc
  match c, hlen with
  | [a, b, c', d, e], _ =>
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at hhl
    subst hhl
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, List.nodup_nil, not_false_eq_true,
      and_true, not_or] at hnd
    exact ⟨a, b, c', d, rfl, hch.1, hch.2.1, hch.2.2.1, hch.2.2.2, hnd.1.2.1, hnd.2.1.2⟩

theorem IsNGon.five {c : List V} (hc : IsNGon Δ 5 c) :
    ∃ x₀ x₁ x₂ x₃ x₄, c = [x₀, x₁, x₂, x₃, x₄, x₀] ∧ Δ.Adj x₀ x₁ ∧ Δ.Adj x₁ x₂ ∧
      Δ.Adj x₂ x₃ ∧ Δ.Adj x₃ x₄ ∧ Δ.Adj x₄ x₀ ∧ x₀ ≠ x₂ ∧ x₀ ≠ x₃ ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧
      x₂ ≠ x₄ := by
  obtain ⟨⟨⟨-, hch⟩, hhl⟩, hlen, hnd⟩ := hc
  match c, hlen with
  | [a, b, c', d, e, f], _ =>
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at hhl
    subst hhl
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, List.nodup_nil, not_false_eq_true,
      and_true, not_or] at hnd
    exact ⟨a, b, c', d, e, rfl, hch.1, hch.2.1, hch.2.2.1, hch.2.2.2.1, hch.2.2.2.2,
      hnd.1.2.1, hnd.1.2.2.1, hnd.2.1.2.1, hnd.2.1.2.2, hnd.2.2.1.2⟩

theorem Moves.backIns (l₁ l₂ : List V) {w v : V} (h : Δ.Adj w v) :
    Moves Δ C (l₁ ++ w :: l₂) (l₁ ++ w :: v :: w :: l₂) :=
  Relation.ReflTransGen.single (ElemMove.backIns l₁ l₂ w v h)

theorem reachable_of_isChain : ∀ {a : V} {l : List V}, (a :: l).IsChain Δ.Adj →
    ∀ b ∈ a :: l, Δ.Reachable a b
  | a, [], _, b, hb => by simp at hb; subst hb; rfl
  | a, c :: l, h, b, hb => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.mp hb with rfl | hb
    · rfl
    · exact h.1.reachable.trans (reachable_of_isChain h.2 b hb)

theorem inClosure_ngons_of_dist_le (d : ℕ) (hd : ∀ u v, Δ.dist u v ≤ d) {c : List V}
    (hc : IsCycle Δ c) : InClosure Δ {p | ∃ n ≤ 2 * d + 1, IsNGon Δ n p} c := by
  set S : Set (List V) := {p | ∃ n ≤ 2 * d + 1, IsNGon Δ n p} with hS
  suffices H : ∀ N, ∀ c, IsCycle Δ c → c.length ≤ N → InClosure Δ S c from
    H c.length c hc le_rfl
  intro N
  induction N with
  | zero =>
    intro c hc hlen
    exact absurd (List.length_eq_zero_iff.mp (by omega)) hc.1.1
  | succ N ih =>
    intro c hc hlen
    by_cases hlt : c.length ≤ N
    · exact ih c hc hlt
    have hlen' : c.length = N + 1 := by omega
    by_cases hshort : c.length ≤ 2 * d + 2
    · by_cases hnd : c.dropLast.Nodup
      ·
        exact inClosure_of_mem hc ⟨c.length - 1, by omega, hc, by omega, hnd⟩
      ·
        obtain ⟨P, a, Q, R, hPQR⟩ := exists_dup_split hnd
        have hne : c ≠ [] := hc.1.1
        have e0 := List.dropLast_append_getLast hne
        rw [hPQR] at e0
        set ℓ := c.getLast hne
        have hc_eq : c = P ++ a :: (Q ++ a :: (R ++ [ℓ])) := by rw [← e0]; simp
        clear_value ℓ
        subst hc_eq
        obtain ⟨⟨-, hch⟩, hhl⟩ := hc
        have hch1 := (List.isChain_split.mp hch)
        have hch2 : (a :: Q ++ a :: (R ++ [ℓ])).IsChain Δ.Adj := by simpa using hch1.2
        rw [List.isChain_split] at hch2
        have hS1 : IsCycle Δ (a :: (Q ++ [a])) := by
          refine ⟨⟨List.cons_ne_nil _ _, by simpa using hch2.1⟩, ?_⟩
          rw [List.head?_cons, ← List.cons_append, List.getLast?_concat]
        have hS1c : InClosure Δ S (a :: (Q ++ [a])) :=
          ih _ hS1 (by simp at hlen' ⊢; omega)
        have m1 : Moves Δ S (P ++ a :: (Q ++ a :: (R ++ [ℓ]))) (P ++ a :: (R ++ [ℓ])) := by
          have := (hS1c.moves_head rfl).context P (R ++ [ℓ])
          simpa using this
        have hS2 : IsCycle Δ (P ++ a :: (R ++ [ℓ])) := by
          refine ⟨⟨by simp, ?_⟩, ?_⟩
          · rw [List.isChain_split]; exact ⟨hch1.1, hch2.2⟩
          · rw [show P ++ a :: (R ++ [ℓ]) = (P ++ a :: R) ++ [ℓ] by simp, List.getLast?_concat]
            rw [show P ++ a :: (Q ++ a :: (R ++ [ℓ])) = (P ++ a :: (Q ++ a :: R)) ++ [ℓ] by simp,
              List.getLast?_concat] at hhl
            rw [← hhl]
            cases P <;> simp
        obtain ⟨w, hw⟩ := ih _ hS2 (by simp at hlen' ⊢; omega)
        exact ⟨w, m1.trans hw⟩
    ·
      have hd1 : d + 1 < c.length := by omega
      obtain ⟨A, w, B, hc_eq, hAlen⟩ : ∃ A w B, c = A ++ w :: B ∧ A.length = d + 1 := by
        obtain ⟨w, B, hdrop⟩ : ∃ w B, c.drop (d + 1) = w :: B := by
          cases h : c.drop (d + 1) with
          | nil => rw [List.drop_eq_nil_iff] at h; omega
          | cons w B => exact ⟨w, B, rfl⟩
        exact ⟨c.take (d + 1), w, B, by rw [← hdrop, List.take_append_drop], by simp; omega⟩
      subst hc_eq
      obtain ⟨⟨-, hch⟩, hhl⟩ := hc
      obtain ⟨v₀, A', rfl⟩ : ∃ v₀ A', A = v₀ :: A' := by
        cases A with
        | nil => simp at hAlen
        | cons v₀ A' => exact ⟨v₀, A', rfl⟩
      obtain ⟨b, B', rfl⟩ : ∃ b B', B = b :: B' := by
        cases B with
        | nil => simp at hshort hAlen; omega
        | cons b B' => exact ⟨b, B', rfl⟩
      have hBlast : (b :: B').getLast? = some v₀ := by
        rw [show v₀ :: A' ++ w :: b :: B' = (v₀ :: A' ++ [w]) ++ b :: B' by simp,
          List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hhl
        rw [← hhl]; rfl
      have hchA : (v₀ :: A' ++ [w]).IsChain Δ.Adj := (List.isChain_split.mp hch).1
      have hchB : (w :: b :: B').IsChain Δ.Adj := (List.isChain_split.mp hch).2
      have hreach : Δ.Reachable v₀ w := reachable_of_isChain hchA w (by simp)
      obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
      have hγ : p.support = v₀ :: p.support.tail := p.cons_tail_support.symm
      set γt := p.support.tail with hγt
      have hγtlen : γt.length = Δ.dist v₀ w := by
        rw [hγt, List.length_tail, SimpleGraph.Walk.length_support, hp]; omega
      have hγch : (v₀ :: γt).IsChain Δ.Adj := by
        rw [← hγ]; exact p.isChain_adj_support
      have hγlast : (v₀ :: γt).getLast? = some w := by
        rw [← hγ, List.getLast?_eq_some_getLast (by simp), SimpleGraph.Walk.getLast_support]
      clear_value γt
      have hback : Moves Δ S (γt.reverse ++ v₀ :: γt) [w] := by
        have hch' : (γt.reverse ++ [v₀]).IsChain Δ.Adj := by
          rw [show γt.reverse ++ [v₀] = (v₀ :: γt).reverse by simp, List.isChain_reverse]
          exact hγch.imp fun _ _ h => h.symm
        have := Moves.backtrack (C := S) γt.reverse v₀ hch'
        rw [List.reverse_reverse] at this
        have e : (γt.reverse ++ [v₀]).head (by simp) = w := by
          have h1 : (γt.reverse ++ [v₀]).head? = some w := by
            rw [show γt.reverse ++ [v₀] = (v₀ :: γt).reverse by simp, List.head?_reverse,
              hγlast]
          rw [List.head?_eq_some_head (by simp)] at h1
          exact Option.some.inj h1
        rwa [e] at this
      have m1 : Moves Δ S (v₀ :: A' ++ w :: b :: B')
          ((v₀ :: A' ++ γt.reverse ++ [v₀]) ++ (γt ++ b :: B')) := by
        have := hback.symm.context (v₀ :: A') (b :: B')
        simpa using this
      obtain ⟨ρ', hρ⟩ : ∃ ρ', (v₀ :: γt).reverse = w :: ρ' := by
        have h1 : (v₀ :: γt).reverse.head? = some w := by rw [List.head?_reverse, hγlast]
        cases hr : (v₀ :: γt).reverse with
        | nil => simp at hr
        | cons a r => rw [hr] at h1; simp at h1; exact ⟨r, by rw [h1]⟩
      have hC₁cyc : IsCycle Δ (v₀ :: A' ++ γt.reverse ++ [v₀]) := by
        refine ⟨⟨by simp, ?_⟩, ?_⟩
        · rw [show v₀ :: A' ++ γt.reverse ++ [v₀] = v₀ :: A' ++ (v₀ :: γt).reverse by simp, hρ,
            List.isChain_split]
          refine ⟨hchA, ?_⟩
          rw [← hρ, List.isChain_reverse]
          exact hγch.imp fun _ _ h => h.symm
        · rw [List.getLast?_concat]; simp
      have hC₂cyc : IsCycle Δ (v₀ :: (γt ++ b :: B')) := by
        refine ⟨⟨by simp, ?_⟩, ?_⟩
        · rw [show v₀ :: (γt ++ b :: B') = (v₀ :: γt) ++ b :: B' by simp, List.isChain_append]
          refine ⟨hγch, hchB.tail, ?_⟩
          intro x hx y hy
          rw [hγlast] at hx
          simp only [Option.mem_def, Option.some.injEq] at hx
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hx hy
          exact (List.isChain_cons_cons.mp hchB).1
        · rw [List.head?_cons, show v₀ :: (γt ++ b :: B') = (v₀ :: γt) ++ b :: B' by simp,
            List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _), hBlast]
      have hdist : Δ.dist v₀ w ≤ d := hd v₀ w
      simp only [List.length_append, List.length_cons] at hlen' hshort hAlen
      have h1 := (ih _ hC₁cyc (by simp; omega)).moves_head (w := v₀) (by simp)
      have h2 := (ih _ hC₂cyc (by simp; omega)).moves_head (w := v₀) (by simp)
      refine ⟨v₀, m1.trans ((h1.context [] (γt ++ b :: B')).trans ?_)⟩
      simpa using h2

theorem dist_eq_two_of {a b : V} (hr : Δ.Reachable a b) (hab : a ≠ b) (hn : ¬ Δ.Adj a b)
    (hd : Δ.dist a b ≤ 2) : Δ.dist a b = 2 := by
  have h0 : Δ.dist a b ≠ 0 := fun h0 => hab ((hr.dist_eq_zero_iff).mp h0)
  have h1 : Δ.dist a b ≠ 1 := fun h1 => hn (SimpleGraph.dist_eq_one_iff_adj.mp h1)
  omega

theorem moves_common_nbr_step {u w a a' : V} (hua : Δ.Adj u a) (hwa : Δ.Adj w a)
    (hua' : Δ.Adj u a') (hwa' : Δ.Adj w a') (haa' : Δ.Adj a a') (l₁ l₂ : List V) :
    Moves Δ {p | IsNGon Δ 3 p} (l₁ ++ u :: a :: w :: l₂) (l₁ ++ u :: a' :: w :: l₂) := by
  have T1 : IsNGon Δ 3 [u, a', a, u] := isNGon_three hua' haa'.symm hua.symm
  have T2 : IsNGon Δ 3 [a', a, w, a'] := isNGon_three haa'.symm hwa.symm hwa'
  have m1 : Moves Δ {p | IsNGon Δ 3 p} (l₁ ++ u :: a :: w :: l₂)
      (l₁ ++ u :: a' :: a :: u :: a :: w :: l₂) := by
    simpa using Moves.cycIns_mem l₁ (a :: w :: l₂) [u, a', a, u] T1 rfl rfl
  have m2 : Moves Δ {p | IsNGon Δ 3 p} (l₁ ++ u :: a' :: a :: u :: a :: w :: l₂)
      (l₁ ++ u :: a' :: a :: w :: l₂) := by
    simpa using Moves.backDel (C := {p | IsNGon Δ 3 p}) (l₁ ++ [u, a']) (w :: l₂) hua.symm
  have m3 : Moves Δ {p | IsNGon Δ 3 p} (l₁ ++ u :: a' :: a :: w :: l₂)
      (l₁ ++ u :: a' :: a :: w :: a' :: w :: l₂) := by
    simpa using Moves.backIns (C := {p | IsNGon Δ 3 p}) (l₁ ++ [u, a', a]) l₂ hwa'
  have m4 : Moves Δ {p | IsNGon Δ 3 p} (l₁ ++ u :: a' :: a :: w :: a' :: w :: l₂)
      (l₁ ++ u :: a' :: w :: l₂) := by
    simpa using Moves.cycDel_mem (l₁ ++ [u]) (w :: l₂) [a', a, w, a'] T2 rfl rfl
  exact m1.trans (m2.trans (m3.trans m4))

theorem inClosure_fourgon
    (h : ∀ u w, Δ.dist u w = 2 → (Δ.induce {v | Δ.Adj u v ∧ Δ.Adj w v}).Connected)
    {c : List V} (hc : IsNGon Δ 4 c) : InClosure Δ {p | IsNGon Δ 3 p} c := by
  obtain ⟨u, a, w, b, rfl, hua, haw, hwb, hbu, huw, hab⟩ := hc.four
  refine ⟨u, ?_⟩
  by_cases hadj : Δ.Adj u w
  ·
    have m1 : Moves Δ {p | IsNGon Δ 3 p} [u, a, w, b, u] [u, a, w, u, w, b, u] := by
      simpa using Moves.backIns (C := {p | IsNGon Δ 3 p}) [u, a] [b, u] hadj.symm
    have m2 : Moves Δ {p | IsNGon Δ 3 p} [u, a, w, u, w, b, u] [u, w, b, u] := by
      simpa using Moves.cycDel_mem [] [w, b, u] [u, a, w, u]
        (isNGon_three hua haw hadj.symm) rfl rfl
    have m3 : Moves Δ {p | IsNGon Δ 3 p} [u, w, b, u] [u] := by
      simpa using Moves.cycDel_mem [] [] [u, w, b, u] (isNGon_three hadj hwb hbu) rfl rfl
    exact m1.trans (m2.trans m3)
  ·
    have hd2 : Δ.dist u w = 2 := by
      refine dist_eq_two_of (hua.reachable.trans haw.reachable) huw hadj ?_
      have := SimpleGraph.dist_le (SimpleGraph.Walk.cons hua (SimpleGraph.Walk.cons haw .nil))
      simpa using this
    set S : Set V := {v | Δ.Adj u v ∧ Δ.Adj w v}
    have hconn := h u w hd2
    have key : ∀ (x y : S), (Δ.induce S).Walk x y →
        Moves Δ {p | IsNGon Δ 3 p} [u, x, w, b, u] [u, y, w, b, u] := by
      intro x y p
      induction p with
      | nil => exact Relation.ReflTransGen.refl
      | @cons x' y' z' hxy p' ih =>
        have hxy' : Δ.Adj x' y' := by simpa using hxy
        have step : Moves Δ {p | IsNGon Δ 3 p} [u, x', w, b, u] [u, y', w, b, u] := by
          simpa using moves_common_nbr_step x'.2.1 x'.2.2 y'.2.1 y'.2.2 hxy' [] [b, u]
        exact step.trans ih
    obtain ⟨p⟩ := hconn.preconnected ⟨a, hua, haw.symm⟩ ⟨b, hbu.symm, hwb⟩
    have m1 := key _ _ p
    have m2 : Moves Δ {p | IsNGon Δ 3 p} [u, b, w, b, u] [u, b, u] := by
      simpa using Moves.backDel (C := {p | IsNGon Δ 3 p}) [u] [u] hwb.symm
    have m3 : Moves Δ {p | IsNGon Δ 3 p} [u, b, u] [u] := by
      simpa using Moves.backDel (C := {p | IsNGon Δ 3 p}) [] [] hbu.symm
    exact m1.trans (m2.trans m3)

theorem inClosure_fivegon (hd : ∀ u v, Δ.dist u v ≤ 2)
    (h : ∀ x₀ x₁ x₂ x₃, Δ.Adj x₀ x₁ → Δ.Adj x₁ x₂ → Δ.Adj x₂ x₃ → Δ.dist x₀ x₂ = 2 →
      Δ.dist x₀ x₃ = 2 → Δ.dist x₁ x₃ = 2 → ∃ v, Δ.Adj v x₀ ∧ Δ.Adj v x₂ ∧ Δ.Adj v x₃)
    {c : List V} (hc : IsNGon Δ 5 c) :
    InClosure Δ {p | IsNGon Δ 3 p ∨ IsNGon Δ 4 p} c := by
  obtain ⟨x₀, x₁, x₂, x₃, x₄, rfl, h01, h12, h23, h34, h40, n02, n03, n13, n14, n24⟩ := hc.five
  set C : Set (List V) := {p | IsNGon Δ 3 p ∨ IsNGon Δ 4 p}
  refine ⟨x₀, ?_⟩
  have tri : ∀ {a b c : V}, Δ.Adj a b → Δ.Adj b c → Δ.Adj c a → [a, b, c, a] ∈ C :=
    fun hab hbc hca => Or.inl (isNGon_three hab hbc hca)
  have quad : ∀ {a b c d : V}, Δ.Adj a b → Δ.Adj b c → Δ.Adj c d → Δ.Adj d a → a ≠ c →
      b ≠ d → [a, b, c, d, a] ∈ C :=
    fun hab hbc hcd hda hac hbd => Or.inr (isNGon_four hab hbc hcd hda hac hbd)
  by_cases c02 : Δ.Adj x₀ x₂
  · have m1 : Moves Δ C [x₀, x₁, x₂, x₃, x₄, x₀] [x₀, x₁, x₂, x₀, x₂, x₃, x₄, x₀] := by
      simpa using Moves.backIns (C := C) [x₀, x₁] [x₃, x₄, x₀] c02.symm
    have m2 : Moves Δ C [x₀, x₁, x₂, x₀, x₂, x₃, x₄, x₀] [x₀, x₂, x₃, x₄, x₀] := by
      simpa using Moves.cycDel_mem [] [x₂, x₃, x₄, x₀] [x₀, x₁, x₂, x₀] (tri h01 h12 c02.symm)
        rfl rfl
    have m3 : Moves Δ C [x₀, x₂, x₃, x₄, x₀] [x₀] := by
      simpa using Moves.cycDel_mem [] [] [x₀, x₂, x₃, x₄, x₀] (quad c02 h23 h34 h40 n03 n24)
        rfl rfl
    exact m1.trans (m2.trans m3)
  by_cases c13 : Δ.Adj x₁ x₃
  · have m1 : Moves Δ C [x₀, x₁, x₂, x₃, x₄, x₀] [x₀, x₁, x₂, x₃, x₁, x₃, x₄, x₀] := by
      simpa using Moves.backIns (C := C) [x₀, x₁, x₂] [x₄, x₀] c13.symm
    have m2 : Moves Δ C [x₀, x₁, x₂, x₃, x₁, x₃, x₄, x₀] [x₀, x₁, x₃, x₄, x₀] := by
      simpa using Moves.cycDel_mem [x₀] [x₃, x₄, x₀] [x₁, x₂, x₃, x₁] (tri h12 h23 c13.symm)
        rfl rfl
    have m3 : Moves Δ C [x₀, x₁, x₃, x₄, x₀] [x₀] := by
      simpa using Moves.cycDel_mem [] [] [x₀, x₁, x₃, x₄, x₀] (quad h01 c13 h34 h40 n03 n14)
        rfl rfl
    exact m1.trans (m2.trans m3)
  by_cases c24 : Δ.Adj x₂ x₄
  · have m1 : Moves Δ C [x₀, x₁, x₂, x₃, x₄, x₀] [x₀, x₁, x₂, x₃, x₄, x₂, x₄, x₀] := by
      simpa using Moves.backIns (C := C) [x₀, x₁, x₂, x₃] [x₀] c24.symm
    have m2 : Moves Δ C [x₀, x₁, x₂, x₃, x₄, x₂, x₄, x₀] [x₀, x₁, x₂, x₄, x₀] := by
      simpa using Moves.cycDel_mem [x₀, x₁] [x₄, x₀] [x₂, x₃, x₄, x₂] (tri h23 h34 c24.symm)
        rfl rfl
    have m3 : Moves Δ C [x₀, x₁, x₂, x₄, x₀] [x₀] := by
      simpa using Moves.cycDel_mem [] [] [x₀, x₁, x₂, x₄, x₀] (quad h01 h12 c24 h40 n02 n14)
        rfl rfl
    exact m1.trans (m2.trans m3)
  by_cases c30 : Δ.Adj x₃ x₀
  · have m1 : Moves Δ C [x₀, x₁, x₂, x₃, x₄, x₀] [x₀, x₁, x₂, x₃, x₀, x₃, x₄, x₀] := by
      simpa using Moves.backIns (C := C) [x₀, x₁, x₂] [x₄, x₀] c30
    have m2 : Moves Δ C [x₀, x₁, x₂, x₃, x₀, x₃, x₄, x₀] [x₀, x₃, x₄, x₀] := by
      simpa using Moves.cycDel_mem [] [x₃, x₄, x₀] [x₀, x₁, x₂, x₃, x₀]
        (quad h01 h12 h23 c30 n02 n13) rfl rfl
    have m3 : Moves Δ C [x₀, x₃, x₄, x₀] [x₀] := by
      simpa using Moves.cycDel_mem [] [] [x₀, x₃, x₄, x₀] (tri c30.symm h34 h40) rfl rfl
    exact m1.trans (m2.trans m3)
  by_cases c41 : Δ.Adj x₄ x₁
  · have m1 : Moves Δ C [x₀, x₁, x₂, x₃, x₄, x₀] [x₀, x₁, x₂, x₃, x₄, x₁, x₄, x₀] := by
      simpa using Moves.backIns (C := C) [x₀, x₁, x₂, x₃] [x₀] c41
    have m2 : Moves Δ C [x₀, x₁, x₂, x₃, x₄, x₁, x₄, x₀] [x₀, x₁, x₄, x₀] := by
      simpa using Moves.cycDel_mem [x₀] [x₄, x₀] [x₁, x₂, x₃, x₄, x₁]
        (quad h12 h23 h34 c41 n13 n24) rfl rfl
    have m3 : Moves Δ C [x₀, x₁, x₄, x₀] [x₀] := by
      simpa using Moves.cycDel_mem [] [] [x₀, x₁, x₄, x₀] (tri h01 c41.symm h40) rfl rfl
    exact m1.trans (m2.trans m3)
  have r01 := h01.reachable
  have r12 := h12.reachable
  have r23 := h23.reachable
  have d02 : Δ.dist x₀ x₂ = 2 := dist_eq_two_of (r01.trans r12) n02 c02 (hd _ _)
  have d03 : Δ.dist x₀ x₃ = 2 :=
    dist_eq_two_of (r01.trans (r12.trans r23)) n03 (fun h => c30 h.symm) (hd _ _)
  have d13 : Δ.dist x₁ x₃ = 2 := dist_eq_two_of (r12.trans r23) n13 c13 (hd _ _)
  obtain ⟨v, hv0, hv2, hv3⟩ := h x₀ x₁ x₂ x₃ h01 h12 h23 d02 d03 d13
  have nv1 : x₁ ≠ v := fun e => c13 (by rw [e]; exact hv3)
  have nv4 : v ≠ x₄ := fun e => c24 (by rw [← e]; exact hv2.symm)
  have m1 : Moves Δ C [x₀, x₁, x₂, x₃, x₄, x₀] [x₀, x₁, x₂, v, x₂, x₃, x₄, x₀] := by
    simpa using Moves.backIns (C := C) [x₀, x₁] [x₃, x₄, x₀] hv2.symm
  have m2 : Moves Δ C [x₀, x₁, x₂, v, x₂, x₃, x₄, x₀]
      [x₀, x₁, x₂, v, x₀, v, x₂, x₃, x₄, x₀] := by
    simpa using Moves.backIns (C := C) [x₀, x₁, x₂] [x₂, x₃, x₄, x₀] hv0
  have m3 : Moves Δ C [x₀, x₁, x₂, v, x₀, v, x₂, x₃, x₄, x₀] [x₀, v, x₂, x₃, x₄, x₀] := by
    simpa using Moves.cycDel_mem [] [v, x₂, x₃, x₄, x₀] [x₀, x₁, x₂, v, x₀]
      (quad h01 h12 hv2.symm hv0 n02 nv1) rfl rfl
  have m4 : Moves Δ C [x₀, v, x₂, x₃, x₄, x₀] [x₀, v, x₂, x₃, v, x₃, x₄, x₀] := by
    simpa using Moves.backIns (C := C) [x₀, v, x₂] [x₄, x₀] hv3.symm
  have m5 : Moves Δ C [x₀, v, x₂, x₃, v, x₃, x₄, x₀] [x₀, v, x₃, x₄, x₀] := by
    simpa using Moves.cycDel_mem [x₀] [x₃, x₄, x₀] [v, x₂, x₃, v] (tri hv2 h23 hv3.symm) rfl rfl
  have m6 : Moves Δ C [x₀, v, x₃, x₄, x₀] [x₀] := by
    simpa using Moves.cycDel_mem [] [] [x₀, v, x₃, x₄, x₀]
      (quad hv0.symm hv3 h34 h40 n03 nv4) rfl rfl
  exact m1.trans (m2.trans (m3.trans (m4.trans (m5.trans m6))))

theorem moves_of_ngon_le_two {n : ℕ} (hn : n ≤ 2) {c : List V} (hc : IsNGon Δ n c) {w : V}
    (hw : c.head? = some w) : Moves Δ C c [w] := by
  obtain ⟨⟨⟨-, hch⟩, hhl⟩, hlen, -⟩ := hc
  match c, hlen with
  | [a], _ =>
    simp only [List.head?_cons, Option.some.injEq] at hw
    rw [hw]
  | [a, b], _ =>
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at hhl
    subst hhl
    exact absurd rfl (List.isChain_pair.mp hch).ne
  | [a, b, c'], _ =>
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at hhl hw
    subst hhl hw
    have hab : Δ.Adj a b := (List.isChain_cons_cons.mp hch).1
    simpa using Moves.backDel (C := C) [] [] hab
  | _ :: _ :: _ :: _ :: _, h => simp at h; omega

theorem triangulable_of_diam_two (hd : ∀ u v, Δ.dist u v ≤ 2)
    (h2 : ∀ u w, Δ.dist u w = 2 → (Δ.induce {v | Δ.Adj u v ∧ Δ.Adj w v}).Connected)
    (h3 : ∀ x₀ x₁ x₂ x₃, Δ.Adj x₀ x₁ → Δ.Adj x₁ x₂ → Δ.Adj x₂ x₃ → Δ.dist x₀ x₂ = 2 →
      Δ.dist x₀ x₃ = 2 → Δ.dist x₁ x₃ = 2 → ∃ v, Δ.Adj v x₀ ∧ Δ.Adj v x₂ ∧ Δ.Adj v x₃) :
    Triangulable Δ := by
  intro c hc
  have h34 : ∀ d ∈ rotRev {p : List V | IsNGon Δ 3 p ∨ IsNGon Δ 4 p}, ∀ w,
      d.head? = some w → d.getLast? = some w → Moves Δ {p | IsNGon Δ 3 p} d [w] := by
    rintro d ⟨e, he, hr | hr⟩ w hw _
    · rcases he with he | he
      · exact Moves.cycDel_mem (C := {p | IsNGon Δ 3 p}) [] [] d (he.rotation hr) hw
          (by rw [← (he.rotation hr).1.2, hw]) |> fun m => by simpa using m
      · exact (inClosure_fourgon h2 (he.rotation hr)).moves_head hw
    · rcases he with he | he
      · exact Moves.cycDel_mem (C := {p | IsNGon Δ 3 p}) [] [] d (he.reverse.rotation hr) hw
          (by rw [← (he.reverse.rotation hr).1.2, hw]) |> fun m => by simpa using m
      · exact (inClosure_fourgon h2 (he.reverse.rotation hr)).moves_head hw
  refine (inClosure_ngons_of_dist_le 2 hd hc).of_rotRev ?_
  intro d hd' w hw hl
  obtain ⟨n, hn, hdn⟩ := rotRev_ngon_le_subset (Γ := Δ) (2 * 2 + 1) hd'
  rcases (show n ≤ 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 by omega) with h | rfl | rfl | rfl
  · exact moves_of_ngon_le_two h hdn hw
  · simpa using Moves.cycDel_mem (C := {p | IsNGon Δ 3 p}) [] [] d hdn hw hl
  · exact (inClosure_fourgon h2 hdn).moves_head hw
  · exact ((inClosure_fivegon hd h3 hdn).of_rotRev h34).moves_head hw

end CFSG.Quasithin.Asc94
