module

public import CFSG.Quasithin.H13.AS91Sec1Defs
public import CFSG.Quasithin.H13.AS91Sec1Replace
public import CFSG.Quasithin.H13.AS91Sec1Short

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94

universe u

variable {V : Type u} {Δ : SimpleGraph V} {N : ℕ} {R : ℕ → V → V → Prop}

namespace FourGen

abbrev Gons34 (Δ : SimpleGraph V) : Set (List V) := {p | IsNGon Δ 3 p ∨ IsNGon Δ 4 p}

@[expose] def LenIH (Δ : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ c : List V, IsCycle Δ c → c.length < n → InClosure Δ (Gons34 Δ) c

@[expose] def FrontClosed (Δ : SimpleGraph V) (R : ℕ → V → V → Prop) (n t : ℕ) : Prop :=
  ∀ (x₀ x₁ x₂ : V) (rest : List V), IsCycle Δ (x₀ :: x₁ :: x₂ :: rest) →
    (x₀ :: x₁ :: x₂ :: rest).length = n → R t x₀ x₂ →
    InClosure Δ (Gons34 Δ) (x₀ :: x₁ :: x₂ :: rest)

theorem three_mem {p : List V} (h : IsNGon Δ 3 p) : p ∈ Gons34 Δ := Or.inl h

theorem isCycle_of_moves {c c' : List V} (h : Moves Δ (Gons34 Δ) c c') (hc : IsCycle Δ c) :
    IsCycle Δ c' := by
  have hC : ∀ d ∈ rotRev (Gons34 Δ), IsPath Δ d := by
    rintro d ⟨e, he, hr⟩
    have he' : IsCycle Δ e := by rcases he with he | he <;> exact he.1
    rcases hr with hr | hr
    · exact (hr.isCycle he').1.1
    · exact (hr.isCycle he'.reverse).1.1
  exact ⟨h.isPath hC hc.1, by rw [← h.head?_eq, ← h.getLast?_eq]; exact hc.2⟩

theorem inClosure_of_moves_lt {n : ℕ} (IH : LenIH Δ n) {c c' : List V} (hc : IsCycle Δ c)
    (h : Moves Δ (Gons34 Δ) c c') (hlt : c'.length < n) : InClosure Δ (Gons34 Δ) c :=
  let ⟨w, hw⟩ := IH c' (isCycle_of_moves h hc) hlt
  ⟨w, h.trans hw⟩

theorem mono_le (h : HypA Δ N R) {k : ℕ} (hk : k ≤ N) {x y : V} (hxy : R k x y) : R N x y := by
  have key : ∀ m, k ≤ m → m ≤ N → R m x y := by
    intro m hkm
    induction m, hkm using Nat.le_induction with
    | base => intro _; exact hxy
    | succ m hkm ih => intro hm; exact h.mono m (by omega) x y (ih (by omega))
  exact key N hk le_rfl

theorem dist2_of_not_perp {x y z : V} (hxy : Δ.Adj x y) (hyz : Δ.Adj y z) (hp : ¬ Perp Δ x z) :
    Dist2 Δ x z :=
  ⟨fun e => hp (Or.inl e), fun a => hp (Or.inr a), y, hxy, hyz⟩

theorem dist2_symm_of_not_perp {x y z : V} (hxy : Δ.Adj x y) (hyz : Δ.Adj y z)
    (hp : ¬ Perp Δ x z) : Dist2 Δ z x :=
  ⟨fun e => hp (Or.inl e.symm), fun a => hp (Or.inr a.symm), y, hyz.symm, hxy.symm⟩

theorem a2_zero (h : HypA Δ N R) (hN : 0 < N) {x y z : V} (hR : R 1 x y) (hxy : Dist2 Δ x y)
    (hxz : Dist2 Δ x z) :
    ∃ u v, Δ.Adj y u ∧ Δ.Adj x u ∧ Δ.Adj x v ∧ Δ.Adj z v ∧ Perp Δ u v := by
  obtain ⟨u, v, hyu, hxu, hxv, hzv, huv⟩ := h.a2 0 hN x y z hR hxy hxz
  refine ⟨u, v, ?_, hxu, hxv, hzv, (h.zero u v).mp (by simpa using huv)⟩
  rcases (h.zero y u).mp hyu with e | a
  · exact absurd (e ▸ hxu) hxy.2.1
  · exact a

theorem moves_middle_of_square (l₁ l₂ : List V) {x y z w : V} (hxy : Δ.Adj x y) (hyz : Δ.Adj y z)
    (hxw : Δ.Adj x w) (hwz : Δ.Adj w z) :
    Moves Δ (Gons34 Δ) (l₁ ++ x :: y :: z :: l₂) (l₁ ++ x :: w :: z :: l₂) := by
  have hcyc : IsCycle Δ [x, w, z, y, x] :=
    ⟨⟨by simp, by simp [List.isChain_cons_cons, hxw, hwz, hyz.symm, hxy.symm]⟩, rfl⟩
  have hcl : InClosure Δ (Gons34 Δ) ([x, w, z] ++ [x, y, z].reverse.tail) := by
    simpa using inClosure_of_length_le_five hcyc (by simp)
  have hp : IsPath Δ [x, y, z] := ⟨by simp, by simp [List.isChain_cons_cons, hxy, hyz]⟩
  have hq : IsPath Δ [x, w, z] := ⟨by simp, by simp [List.isChain_cons_cons, hxw, hwz]⟩
  simpa using moves_context_of_inClosure hp hq rfl rfl hcl l₁ l₂

theorem exists_moves_of_perp {x y z : V} (hxy : Δ.Adj x y) (hyz : Δ.Adj y z) (hp : Perp Δ x z)
    (l₁ l₂ : List V) :
    ∃ c', Moves Δ (Gons34 Δ) (l₁ ++ x :: y :: z :: l₂) c' ∧
      c'.length < (l₁ ++ x :: y :: z :: l₂).length := by
  rcases hp with rfl | hxz
  · exact ⟨_, Moves.backDel l₁ l₂ hxy, by simp⟩
  · exact ⟨_, moves_triangle_shortcut (fun _ hp => three_mem hp) l₁ l₂ hxy hyz hxz, by simp⟩

theorem inClosure_of_perp_triple {n : ℕ} (IH : LenIH Δ n) {l₁ l₂ : List V} {x y z : V}
    (hc : IsCycle Δ (l₁ ++ x :: y :: z :: l₂)) (hlen : (l₁ ++ x :: y :: z :: l₂).length = n)
    (hxy : Δ.Adj x y) (hyz : Δ.Adj y z) (hp : Perp Δ x z) :
    InClosure Δ (Gons34 Δ) (l₁ ++ x :: y :: z :: l₂) := by
  obtain ⟨c', hm, hl⟩ := exists_moves_of_perp hxy hyz hp l₁ l₂
  exact inClosure_of_moves_lt IH hc hm (by omega)

theorem exists_short_of_five {y₀ y₁ y₂ y₃ y₄ u v : V} (h01 : Δ.Adj y₀ y₁) (h12 : Δ.Adj y₁ y₂)
    (h23 : Δ.Adj y₂ y₃) (h34 : Δ.Adj y₃ y₄) (h0u : Δ.Adj y₀ u) (h2u : Δ.Adj y₂ u)
    (h2v : Δ.Adj y₂ v) (h4v : Δ.Adj y₄ v) (huv : Perp Δ u v) :
    ∃ r, Moves Δ (Gons34 Δ) [y₀, y₁, y₂, y₃, y₄] r ∧ r.length ≤ 4 := by
  have m1 : Moves Δ (Gons34 Δ) [y₀, y₁, y₂, y₃, y₄] [y₀, u, y₂, y₃, y₄] := by
    simpa using moves_middle_of_square [] [y₃, y₄] h01 h12 h0u h2u.symm
  have m2 : Moves Δ (Gons34 Δ) [y₀, u, y₂, y₃, y₄] [y₀, u, y₂, v, y₄] := by
    simpa using moves_middle_of_square [y₀, u] [] h23 h34 h2v h4v.symm
  rcases huv with huv | huv
  · refine ⟨[y₀, u, y₄], m1.trans (m2.trans ?_), by simp⟩
    rw [← huv]
    simpa using Moves.backDel (C := Gons34 Δ) [y₀] [y₄] h2u.symm
  · refine ⟨[y₀, u, v, y₄], m1.trans (m2.trans ?_), by simp⟩
    simpa using moves_triangle_shortcut (fun _ hp => three_mem hp) [y₀] [y₄] h2u.symm h2v huv

theorem exists_short_of_R1 (h : HypA Δ N R) (hN : 0 < N) {y₀ y₁ y₂ y₃ y₄ : V}
    (h01 : Δ.Adj y₀ y₁) (h12 : Δ.Adj y₁ y₂) (h23 : Δ.Adj y₂ y₃) (h34 : Δ.Adj y₃ y₄)
    (hR : R 1 y₀ y₂) : ∃ r, Moves Δ (Gons34 Δ) [y₀, y₁, y₂, y₃, y₄] r ∧ r.length ≤ 4 := by
  by_cases hp : Perp Δ y₀ y₂
  · obtain ⟨r, hr, hl⟩ := exists_moves_of_perp h01 h12 hp [] [y₃, y₄]
    exact ⟨r, by simpa using hr, by simp at hl; omega⟩
  by_cases hq : Perp Δ y₂ y₄
  · obtain ⟨r, hr, hl⟩ := exists_moves_of_perp h23 h34 hq [y₀, y₁] []
    exact ⟨r, by simpa using hr, by simp at hl; omega⟩
  obtain ⟨u, v, h0u, h2u, h2v, h4v, huv⟩ := a2_zero h hN (h.symm 1 y₀ y₂ hR)
    (dist2_symm_of_not_perp h01 h12 hp) (dist2_of_not_perp h23 h34 hq)
  exact exists_short_of_five h01 h12 h23 h34 h0u h2u h2v h4v huv

theorem exists_short_bridge (h : HypA Δ N R) (hN : 0 < N) {u x₂ x₃ x₄ x₅ v : V}
    (hu2 : Δ.Adj u x₂) (h23 : Δ.Adj x₂ x₃) (h34 : Δ.Adj x₃ x₄) (h45 : Δ.Adj x₄ x₅)
    (h2v : Δ.Adj x₂ v) (h4v : Δ.Adj x₄ v) (huv : R 1 u v) :
    ∃ r, Moves Δ (Gons34 Δ) [u, x₂, x₃, x₄, x₅] r ∧ r.length ≤ 4 := by
  have m1 : Moves Δ (Gons34 Δ) [u, x₂, x₃, x₄, x₅] [u, x₂, v, x₄, x₅] := by
    simpa using moves_middle_of_square [u] [x₅] h23 h34 h2v h4v.symm
  obtain ⟨r, hr, hl⟩ := exists_short_of_R1 h hN hu2 h2v h4v.symm h45 huv
  exact ⟨r, m1.trans hr, hl⟩

theorem inClosure_of_five {n : ℕ} (IH : LenIH Δ n) {x₀ x₁ x₂ x₃ x₄ u v : V} {rest : List V}
    (hc : IsCycle Δ (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: rest))
    (hlen : (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: rest).length = n)
    (h01 : Δ.Adj x₀ x₁) (h12 : Δ.Adj x₁ x₂) (h23 : Δ.Adj x₂ x₃) (h34 : Δ.Adj x₃ x₄)
    (h0u : Δ.Adj x₀ u) (h2u : Δ.Adj x₂ u) (h2v : Δ.Adj x₂ v) (h4v : Δ.Adj x₄ v)
    (huv : Perp Δ u v) : InClosure Δ (Gons34 Δ) (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: rest) := by
  obtain ⟨r, hr, hl⟩ := exists_short_of_five h01 h12 h23 h34 h0u h2u h2v h4v huv
  have hm : Moves Δ (Gons34 Δ) (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: rest) (r ++ rest) := by
    simpa using hr.context [] rest
  exact inClosure_of_moves_lt IH hc hm (by simp at hlen ⊢; omega)

theorem inClosure_of_adj_case {n : ℕ} (IH : LenIH Δ n) {x₀ x₁ x₂ x₃ x₄ x₅ u : V}
    {rest : List V} (hc : IsCycle Δ (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: rest))
    (hlen : (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: rest).length = n)
    (h01 : Δ.Adj x₀ x₁) (h12 : Δ.Adj x₁ x₂) (h0u : Δ.Adj x₀ u) (h2u : Δ.Adj x₂ u)
    {r : List V} (hr : Moves Δ (Gons34 Δ) [u, x₂, x₃, x₄, x₅] r) (hl : r.length ≤ 4) :
    InClosure Δ (Gons34 Δ) (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: rest) := by
  have m1 : Moves Δ (Gons34 Δ) (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: rest)
      (x₀ :: u :: x₂ :: x₃ :: x₄ :: x₅ :: rest) := by
    simpa using moves_middle_of_square [] (x₃ :: x₄ :: x₅ :: rest) h01 h12 h0u h2u.symm
  have m2 : Moves Δ (Gons34 Δ) (x₀ :: u :: x₂ :: x₃ :: x₄ :: x₅ :: rest) (x₀ :: (r ++ rest)) := by
    simpa using hr.context [x₀] rest
  exact inClosure_of_moves_lt IH hc (m1.trans m2) (by simp at hlen ⊢; omega)

theorem inClosure_of_two_step_case {n t : ℕ} (hn : 6 ≤ n) (IH : LenIH Δ n)
    (Tt : FrontClosed Δ R n t) {x₀ x₁ x₂ x₃ x₄ x₅ y u : V} {rest : List V}
    (hc : IsCycle Δ (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: rest))
    (hlen : (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: rest).length = n)
    (h01 : Δ.Adj x₀ x₁) (h12 : Δ.Adj x₁ x₂) (h0y : Δ.Adj x₀ y) (hyu : Δ.Adj y u)
    (h2u : Δ.Adj x₂ u) (hRu : R t x₀ u) {r : List V}
    (hr : Moves Δ (Gons34 Δ) [u, x₂, x₃, x₄, x₅] r) (hl : r.length ≤ 4) :
    InClosure Δ (Gons34 Δ) (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: rest) := by
  have hd : IsCycle Δ [x₀, y, u, x₂, x₁, x₀] :=
    ⟨⟨by simp, by simp [List.isChain_cons_cons, h0y, hyu, h2u.symm, h12.symm, h01.symm]⟩, rfl⟩
  have hdc : InClosure Δ (Gons34 Δ) [x₀, y, u, x₂, x₁, x₀] := by
    rcases Nat.lt_or_ge 6 n with h6 | h6
    · exact IH _ hd (by simpa using h6)
    · exact Tt x₀ y u [x₂, x₁, x₀] hd (by simp; omega) hRu
  have hp : IsPath Δ [x₀, x₁, x₂] := ⟨by simp, by simp [List.isChain_cons_cons, h01, h12]⟩
  have hq : IsPath Δ [x₀, y, u, x₂] :=
    ⟨by simp, by simp [List.isChain_cons_cons, h0y, hyu, h2u.symm]⟩
  have m1 : Moves Δ (Gons34 Δ) (x₀ :: x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: rest)
      (x₀ :: y :: u :: x₂ :: x₃ :: x₄ :: x₅ :: rest) := by
    simpa using moves_context_of_inClosure hp hq rfl rfl (by simpa using hdc) []
      (x₃ :: x₄ :: x₅ :: rest)
  obtain ⟨r₁, rfl⟩ : ∃ r₁, r = u :: r₁ := List.head?_eq_some_iff.mp (hr.head?_eq.symm)
  have m2 : Moves Δ (Gons34 Δ) (x₀ :: y :: u :: x₂ :: x₃ :: x₄ :: x₅ :: rest)
      (x₀ :: y :: u :: (r₁ ++ rest)) := by
    simpa using hr.context [x₀, y] rest
  have hc' : IsCycle Δ (x₀ :: y :: u :: (r₁ ++ rest)) := isCycle_of_moves (m1.trans m2) hc
  by_cases hlt : (x₀ :: y :: u :: (r₁ ++ rest)).length < n
  · exact inClosure_of_moves_lt IH hc (m1.trans m2) hlt
  · have hlen' : (x₀ :: y :: u :: (r₁ ++ rest)).length = n := by
      simp at hlen hl hlt ⊢; omega
    obtain ⟨w, hw⟩ := Tt x₀ y u (r₁ ++ rest) hc' hlen' hRu
    exact ⟨w, (m1.trans m2).trans hw⟩

theorem frontClosed_zero (h : HypA Δ N R) {n : ℕ} (IH : LenIH Δ n) : FrontClosed Δ R n 0 := by
  intro x₀ x₁ x₂ rest hc hlen hR
  have hch := hc.1.2
  simp only [List.isChain_cons_cons] at hch
  exact inClosure_of_perp_triple (l₁ := []) IH hc hlen hch.1 hch.2.1 ((h.zero x₀ x₂).mp hR)

theorem frontClosed_succ (h : HypA Δ N R) {n t : ℕ} (hn : 6 ≤ n) (ht : t < N) (IH : LenIH Δ n)
    (Tt : FrontClosed Δ R n t) : FrontClosed Δ R n (t + 1) := by
  intro x₀ x₁ x₂ rest hc hlen hR
  obtain ⟨x₃, x₄, x₅, rest, rfl⟩ : ∃ x₃ x₄ x₅ rest', rest = x₃ :: x₄ :: x₅ :: rest' := by
    rcases rest with _ | ⟨x₃, _ | ⟨x₄, _ | ⟨x₅, rest'⟩⟩⟩
    · simp at hlen; omega
    · simp at hlen; omega
    · simp at hlen; omega
    · exact ⟨x₃, x₄, x₅, rest', rfl⟩
  have hch := hc.1.2
  simp only [List.isChain_cons_cons] at hch
  obtain ⟨h01, h12, h23, h34, h45, -⟩ := hch
  by_cases hp02 : Perp Δ x₀ x₂
  · exact inClosure_of_perp_triple (l₁ := []) IH hc hlen h01 h12 hp02
  by_cases hp24 : Perp Δ x₂ x₄
  · exact inClosure_of_perp_triple (l₁ := [x₀, x₁]) IH hc hlen h23 h34 hp24
  obtain ⟨u, v, hRu, h2u, h2v, h4v, huv⟩ := h.a2 t ht x₂ x₀ x₄ (h.symm _ _ _ hR)
    (dist2_symm_of_not_perp h01 h12 hp02) (dist2_of_not_perp h23 h34 hp24)
  rcases t with _ | t
  · have h0u : Δ.Adj x₀ u := by
      rcases (h.zero x₀ u).mp hRu with e | a
      · exact absurd (e ▸ h2u) (dist2_symm_of_not_perp h01 h12 hp02).2.1
      · exact a
    exact inClosure_of_five IH hc hlen h01 h12 h23 h34 h0u h2u h2v h4v
      ((h.zero u v).mp (by simpa using huv))
  · have hmin : min (t + 1) 1 = 1 := by omega
    rw [hmin] at huv
    obtain ⟨r, hr, hl⟩ := exists_short_bridge h (by omega) h2u.symm h23 h34 h45 h2v h4v huv
    rcases (h.top x₀ u).mp (mono_le h (by omega) hRu) with (e | h0u) | ⟨y, h0y, hyu⟩
    · exact absurd (e ▸ h2u) (dist2_symm_of_not_perp h01 h12 hp02).2.1
    · exact inClosure_of_adj_case IH hc hlen h01 h12 h0u h2u hr hl
    · exact inClosure_of_two_step_case hn IH Tt hc hlen h01 h12 h0y hyu h2u hRu hr hl

theorem frontClosed_of_le (h : HypA Δ N R) {n : ℕ} (hn : 6 ≤ n) (IH : LenIH Δ n) :
    ∀ t, t ≤ N → FrontClosed Δ R n t
  | 0, _ => frontClosed_zero h IH
  | t + 1, ht => frontClosed_succ h hn (by omega) IH (frontClosed_of_le h hn IH t (by omega))

theorem inClosure_of_length (h : HypA Δ N R) :
    ∀ n, ∀ c : List V, IsCycle Δ c → c.length = n → InClosure Δ (Gons34 Δ) c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro c hc hlen
    by_cases hn : n ≤ 5
    · exact inClosure_of_length_le_five hc (by omega)
    · have IH' : LenIH Δ n := fun c' hc' hlt => IH _ hlt c' hc' rfl
      obtain ⟨x₀, x₁, x₂, rest, rfl⟩ : ∃ x₀ x₁ x₂ rest, c = x₀ :: x₁ :: x₂ :: rest := by
        rcases c with _ | ⟨x₀, _ | ⟨x₁, _ | ⟨x₂, rest⟩⟩⟩
        · simp at hlen; omega
        · simp at hlen; omega
        · simp at hlen; omega
        · exact ⟨x₀, x₁, x₂, rest, rfl⟩
      have hch := hc.1.2
      simp only [List.isChain_cons_cons] at hch
      exact frontClosed_of_le h (by omega) IH' N le_rfl x₀ x₁ x₂ rest hc hlen
        ((h.top x₀ x₂).mpr (Or.inr ⟨x₁, hch.1, hch.2.1⟩))

end FourGen

theorem fourGenerated_of_hypA {N : ℕ} {R : ℕ → V → V → Prop} (h : HypA Δ N R) :
    FourGenerated Δ :=
  fun c hc => FourGen.inClosure_of_length h c.length c hc rfl

end CFSG.Quasithin.H13.AS91
