module

public import CFSG.Quasithin.Recognition.UniquenessSystemDefs

public section

namespace CFSG.Quasithin.Asc94

universe u

variable {V : Type u} {Γ : SimpleGraph V} {C C' : Set (List V)}

namespace ElemMove

theorem symm {p q : List V} (h : ElemMove Γ C p q) : ElemMove Γ C q p := by
  cases h with
  | backDel l₁ l₂ w v h => exact backIns l₁ l₂ w v h
  | backIns l₁ l₂ w v h => exact backDel l₁ l₂ w v h
  | cycIns l₁ l₂ c w hc h₁ h₂ => exact cycDel l₁ l₂ c w hc h₁ h₂
  | cycDel l₁ l₂ c w hc h₁ h₂ => exact cycIns l₁ l₂ c w hc h₁ h₂

theorem context {p q : List V} (h : ElemMove Γ C p q) (a b : List V) :
    ElemMove Γ C (a ++ p ++ b) (a ++ q ++ b) := by
  cases h with
  | backDel l₁ l₂ w v h => simpa using backDel (C := C) (a ++ l₁) (l₂ ++ b) w v h
  | backIns l₁ l₂ w v h => simpa using backIns (C := C) (a ++ l₁) (l₂ ++ b) w v h
  | cycIns l₁ l₂ c w hc h₁ h₂ => simpa using cycIns (Γ := Γ) (a ++ l₁) (l₂ ++ b) c w hc h₁ h₂
  | cycDel l₁ l₂ c w hc h₁ h₂ => simpa using cycDel (Γ := Γ) (a ++ l₁) (l₂ ++ b) c w hc h₁ h₂

end ElemMove

namespace Moves

theorem symm {p q : List V} (h : Moves Γ C p q) : Moves Γ C q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hm ih => exact (Relation.ReflTransGen.single hm.symm).trans ih

theorem context {p q : List V} (h : Moves Γ C p q) (a b : List V) :
    Moves Γ C (a ++ p ++ b) (a ++ q ++ b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hm ih => exact ih.tail (hm.context a b)

theorem backDel (l₁ l₂ : List V) {w v : V} (h : Γ.Adj w v) :
    Moves Γ C (l₁ ++ w :: v :: w :: l₂) (l₁ ++ w :: l₂) :=
  Relation.ReflTransGen.single (ElemMove.backDel l₁ l₂ w v h)

theorem cycDel_mem (l₁ l₂ : List V) {w : V} (c : List V) (hc : c ∈ C) (hcyc : c.head? = some w)
    (hlast : c.getLast? = some w) : Moves Γ C (l₁ ++ c ++ l₂) (l₁ ++ w :: l₂) := by
  refine Relation.ReflTransGen.single (ElemMove.cycDel l₁ l₂ c w ⟨c, hc, Or.inl ?_⟩ hcyc hlast)
  obtain ⟨a, s, rfl⟩ : ∃ a s, c = a :: s := by
    cases c with
    | nil => simp at hcyc
    | cons a s => exact ⟨a, s, rfl⟩
  refine ⟨a :: s, [], w, by simp, hlast, ?_⟩
  simp only [List.head?_cons, Option.some.injEq] at hcyc
  simp [hcyc]

theorem cycIns_mem (l₁ l₂ : List V) {w : V} (c : List V) (hc : c ∈ C) (hcyc : c.head? = some w)
    (hlast : c.getLast? = some w) : Moves Γ C (l₁ ++ w :: l₂) (l₁ ++ c ++ l₂) :=
  (cycDel_mem l₁ l₂ c hc hcyc hlast).symm

theorem backtrack : ∀ (q : List V) (w : V), (q ++ [w]).IsChain Γ.Adj →
    Moves Γ C (q ++ w :: q.reverse) [(q ++ [w]).head (by simp)] := by
  intro q
  induction q using List.reverseRecOn with
  | nil => intro w _; exact Relation.ReflTransGen.refl
  | append_singleton q v ih =>
    intro w hq
    have hvw : Γ.Adj v w := by
      rw [List.append_assoc, List.singleton_append, List.isChain_append_cons_cons] at hq
      exact hq.2.1
    have hq' : (q ++ [v]).IsChain Γ.Adj := by
      rw [List.append_assoc, List.singleton_append, List.isChain_split] at hq
      exact hq.1
    have e : (q ++ [v]) ++ w :: (q ++ [v]).reverse = q ++ v :: w :: v :: q.reverse := by simp
    have e2 : (q ++ [v] ++ [w]).head (by simp) = (q ++ [v]).head (by simp) := by
      cases q <;> simp
    rw [e, e2]
    exact (backDel q q.reverse hvw).trans (ih v hq')

end Moves

theorem ElemMove.head?_eq {p q : List V} (h : ElemMove Γ C p q) : p.head? = q.head? := by
  cases h with
  | backDel l₁ l₂ w v h => cases l₁ <;> simp
  | backIns l₁ l₂ w v h => cases l₁ <;> simp
  | cycIns l₁ l₂ c w hc h₁ h₂ =>
    cases l₁ with
    | nil => cases c with
      | nil => simp at h₁
      | cons a c => simp at h₁; simp [h₁]
    | cons a l₁ => simp
  | cycDel l₁ l₂ c w hc h₁ h₂ =>
    cases l₁ with
    | nil => cases c with
      | nil => simp at h₁
      | cons a c => simp at h₁; simp [h₁]
    | cons a l₁ => simp

theorem Moves.head?_eq {p q : List V} (h : Moves Γ C p q) : p.head? = q.head? := by
  induction h with
  | refl => rfl
  | tail _ hm ih => exact ih.trans hm.head?_eq

theorem InClosure.moves_head {c : List V} {w : V} (h : InClosure Γ C c) (hw : c.head? = some w) :
    Moves Γ C c [w] := by
  obtain ⟨w', hw'⟩ := h
  have := hw'.head?_eq
  rw [hw] at this
  simp only [List.head?_cons, Option.some.injEq] at this
  rw [this]
  exact hw'

theorem exists_cons_concat_of_head_last {c : List V} {w : V} (h₁ : c.head? = some w)
    (h₂ : c.getLast? = some w) : (∃ c₁, c = w :: c₁) ∧ ∃ c₀, c = c₀ ++ [w] := by
  refine ⟨?_, ?_⟩
  · cases c with
    | nil => simp at h₁
    | cons a c₁ => simp only [List.head?_cons, Option.some.injEq] at h₁; exact ⟨c₁, by rw [h₁]⟩
  · rcases c.eq_nil_or_concat' with rfl | ⟨c₀, b, rfl⟩
    · simp at h₁
    · rw [List.getLast?_concat, Option.some.injEq] at h₂; exact ⟨c₀, by rw [h₂]⟩

theorem ElemMove.isPath (hC : ∀ c ∈ rotRev C, IsPath Γ c) {p q : List V}
    (h : ElemMove Γ C p q) (hp : IsPath Γ p) : IsPath Γ q := by
  obtain ⟨-, hch⟩ := hp
  refine ⟨?_, ?_⟩
  · cases h with
    | backDel l₁ l₂ w v h => simp
    | backIns l₁ l₂ w v h => simp
    | cycIns l₁ l₂ c w hc h₁ h₂ =>
      obtain ⟨⟨c₁, rfl⟩, -⟩ := exists_cons_concat_of_head_last h₁ h₂; simp
    | cycDel l₁ l₂ c w hc h₁ h₂ => simp
  · cases h with
    | backDel l₁ l₂ w v h =>
      rw [List.isChain_split] at hch ⊢
      exact ⟨hch.1, hch.2.tail.tail⟩
    | backIns l₁ l₂ w v h =>
      rw [List.isChain_split] at hch ⊢
      refine ⟨hch.1, ?_⟩
      rw [List.isChain_cons_cons, List.isChain_cons_cons]
      exact ⟨h, h.symm, hch.2⟩
    | cycIns l₁ l₂ c w hc h₁ h₂ =>
      obtain ⟨⟨c₁, hc₁⟩, ⟨c₀, hc₀⟩⟩ := exists_cons_concat_of_head_last h₁ h₂
      rw [List.isChain_split] at hch
      have hcc : c.IsChain Γ.Adj := (hC c hc).2
      rw [hc₀, show l₁ ++ (c₀ ++ [w]) ++ l₂ = (l₁ ++ c₀) ++ w :: l₂ by simp, List.isChain_split]
      refine ⟨?_, hch.2⟩
      rw [show l₁ ++ c₀ ++ [w] = l₁ ++ c by rw [hc₀]; simp, hc₁, List.isChain_split]
      exact ⟨hch.1, hc₁ ▸ hcc⟩
    | cycDel l₁ l₂ c w hc h₁ h₂ =>
      obtain ⟨⟨c₁, hc₁⟩, ⟨c₀, hc₀⟩⟩ := exists_cons_concat_of_head_last h₁ h₂
      rw [List.isChain_split]
      refine ⟨?_, ?_⟩
      · have := hch
        rw [hc₁, show l₁ ++ w :: c₁ ++ l₂ = l₁ ++ w :: (c₁ ++ l₂) by simp,
          List.isChain_split] at this
        exact this.1
      · rw [hc₀, show l₁ ++ (c₀ ++ [w]) ++ l₂ = (l₁ ++ c₀) ++ w :: l₂ by simp,
          List.isChain_split] at hch
        exact hch.2

theorem Moves.isPath (hC : ∀ c ∈ rotRev C, IsPath Γ c) {p q : List V} (h : Moves Γ C p q)
    (hp : IsPath Γ p) : IsPath Γ q := by
  induction h with
  | refl => exact hp
  | tail _ hm ih => exact hm.isPath hC ih

theorem Moves.of_rotRev {p q : List V} (h : Moves Γ C p q)
    (hC : ∀ d ∈ rotRev C, ∀ w, d.head? = some w → d.getLast? = some w → Moves Γ C' d [w]) :
    Moves Γ C' p q := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hm ih =>
    refine ih.trans ?_
    cases hm with
    | backDel l₁ l₂ w v h => exact Relation.ReflTransGen.single (.backDel l₁ l₂ w v h)
    | backIns l₁ l₂ w v h => exact Relation.ReflTransGen.single (.backIns l₁ l₂ w v h)
    | cycIns l₁ l₂ c w hc h₁ h₂ =>
      have := ((hC c hc w h₁ h₂).symm).context l₁ l₂
      simpa using this
    | cycDel l₁ l₂ c w hc h₁ h₂ =>
      have := (hC c hc w h₁ h₂).context l₁ l₂
      simpa using this

theorem InClosure.of_rotRev {c : List V} (h : InClosure Γ C c)
    (hC : ∀ d ∈ rotRev C, ∀ w, d.head? = some w → d.getLast? = some w → Moves Γ C' d [w]) :
    InClosure Γ C' c :=
  let ⟨w, hw⟩ := h
  ⟨w, hw.of_rotRev hC⟩

theorem isRotation_iff {c d : List V} :
    IsRotation c d ↔ ∃ (a : V) (A B : List V), c = a :: (A ++ B) ∧
      d = (a :: A).getLast (List.cons_ne_nil a A) :: (B ++ A) := by
  constructor
  · rintro ⟨l₁, l₂, w, rfl, hw, rfl⟩
    cases l₁ with
    | nil => simp at hw
    | cons a A =>
      refine ⟨a, A, l₂, rfl, ?_⟩
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a A), Option.some.injEq] at hw
      rw [← hw]
      rfl
  · rintro ⟨a, A, B, rfl, rfl⟩
    exact ⟨a :: A, B, _, rfl, List.getLast?_eq_some_getLast _, rfl⟩

theorem IsCycle.eq_cons {c : List V} (hc : IsCycle Γ c) :
    ∃ a s, c = [a] ∨ c = a :: (s ++ [a]) := by
  obtain ⟨⟨hne, -⟩, hhl⟩ := hc
  cases c with
  | nil => exact absurd rfl hne
  | cons a t =>
    rcases t.eq_nil_or_concat' with rfl | ⟨s, b, rfl⟩
    · exact ⟨a, [], Or.inl rfl⟩
    · have hb : b = a := by
        rw [List.head?_cons, ← List.cons_append, List.getLast?_concat] at hhl
        exact (Option.some.inj hhl).symm
      subst hb
      exact ⟨b, s, Or.inr rfl⟩

theorem IsRotation.cases {c d : List V} (hr : IsRotation c d) (hc : IsCycle Γ c) :
    d = c ∨ ∃ (a w : V) (A' B' : List V), c = a :: (A' ++ w :: (B' ++ [a])) ∧
      d = w :: (B' ++ a :: (A' ++ [w])) := by
  obtain ⟨a, A, B, rfl, rfl⟩ := isRotation_iff.mp hr
  rcases A.eq_nil_or_concat' with rfl | ⟨A', w, rfl⟩ <;>
    rcases B.eq_nil_or_concat' with rfl | ⟨B', b, rfl⟩
  · left; rfl
  · left; simp
  · left
    have hhl := hc.2
    simp only [List.append_nil, List.head?_cons] at hhl
    rw [← List.cons_append, List.getLast?_concat] at hhl
    have hwa : w = a := (Option.some.inj hhl).symm
    subst hwa
    rw [List.getLast_cons (by simp), List.getLast_append_singleton]
    simp
  · right
    have hhl := hc.2
    simp only [List.head?_cons] at hhl
    rw [show a :: (A' ++ [w] ++ (B' ++ [b])) = (a :: (A' ++ [w] ++ B')) ++ [b] by simp,
      List.getLast?_concat] at hhl
    have hba : b = a := (Option.some.inj hhl).symm
    subst hba
    refine ⟨b, w, A', B', by simp, ?_⟩
    rw [List.getLast_cons (by simp), List.getLast_append_singleton]
    simp

theorem IsRotation.isCycle {c d : List V} (hr : IsRotation c d) (hc : IsCycle Γ c) :
    IsCycle Γ d ∧ (∀ v ∈ d, v ∈ c) ∧ d.length = c.length := by
  rcases hr.cases hc with rfl | ⟨a, w, A', B', rfl, rfl⟩
  · exact ⟨hc, fun _ h => h, rfl⟩
  refine ⟨⟨⟨List.cons_ne_nil _ _, ?_⟩, ?_⟩, ?_, by simp; omega⟩
  · have hch := hc.1.2
    rw [show a :: (A' ++ w :: (B' ++ [a])) = (a :: A') ++ w :: (B' ++ [a]) by simp,
      List.isChain_split] at hch
    rw [show w :: (B' ++ a :: (A' ++ [w])) = (w :: B') ++ a :: (A' ++ [w]) by simp,
      List.isChain_split]
    exact ⟨by simpa using hch.2, by simpa using hch.1⟩
  · rw [List.head?_cons, show w :: (B' ++ a :: (A' ++ [w])) = (w :: (B' ++ a :: A')) ++ [w] by
      simp, List.getLast?_concat]
  · intro v hv
    simp only [List.mem_cons, List.mem_append] at hv ⊢
    tauto

theorem IsCycle.reverse {c : List V} (hc : IsCycle Γ c) : IsCycle Γ c.reverse := by
  obtain ⟨⟨hne, hch⟩, hhl⟩ := hc
  refine ⟨⟨by simpa using hne, ?_⟩, ?_⟩
  · rw [List.isChain_reverse]
    exact hch.imp fun _ _ h => h.symm
  · rw [List.head?_reverse, List.getLast?_reverse, hhl]

theorem IsNGon.rotation {n : ℕ} {c d : List V} (hc : IsNGon Γ n c) (hr : IsRotation c d) :
    IsNGon Γ n d := by
  obtain ⟨hcyc, hlen, hnd⟩ := hc
  obtain ⟨hdc, -, hdl⟩ := hr.isCycle hcyc
  refine ⟨hdc, by rw [hdl, hlen], ?_⟩
  rcases hr.cases hcyc with rfl | ⟨a, w, A', B', rfl, rfl⟩
  · exact hnd
  rw [show a :: (A' ++ w :: (B' ++ [a])) = (a :: (A' ++ w :: B')) ++ [a] by simp,
    List.dropLast_concat] at hnd
  rw [show w :: (B' ++ a :: (A' ++ [w])) = (w :: (B' ++ a :: A')) ++ [w] by simp,
    List.dropLast_concat]
  have hp : (w :: (B' ++ a :: A')).Perm (a :: (A' ++ w :: B')) := by
    have := (List.perm_append_comm (l₁ := w :: B') (l₂ := a :: A'))
    simpa using this
  exact hp.nodup_iff.mpr hnd

theorem IsNGon.reverse {n : ℕ} {c : List V} (hc : IsNGon Γ n c) : IsNGon Γ n c.reverse := by
  obtain ⟨hcyc, hlen, hnd⟩ := hc
  refine ⟨hcyc.reverse, by simp [hlen], ?_⟩
  obtain ⟨a, s, rfl | rfl⟩ := hcyc.eq_cons
  · simp
  · rw [← List.cons_append, List.dropLast_concat] at hnd
    rw [show (a :: (s ++ [a])).reverse = (a :: s.reverse) ++ [a] by simp, List.dropLast_concat]
    exact (List.Perm.cons a (List.reverse_perm s)).nodup_iff.mpr hnd

theorem rotRev_ngon_subset (S : Set ℕ) :
    rotRev {p : List V | ∃ n ∈ S, IsNGon Γ n p} ⊆ {p | ∃ n ∈ S, IsNGon Γ n p} := by
  rintro d ⟨c, ⟨n, hn, hc⟩, hr | hr⟩
  · exact ⟨n, hn, hc.rotation hr⟩
  · exact ⟨n, hn, hc.reverse.rotation hr⟩

theorem rotRev_ngon_le_subset (k : ℕ) :
    rotRev {p : List V | ∃ n ≤ k, IsNGon Γ n p} ⊆ {p | ∃ n ≤ k, IsNGon Γ n p} :=
  rotRev_ngon_subset (Set.Iic k)

theorem rotRev_ngon_eq_subset (n : ℕ) :
    rotRev {p : List V | IsNGon Γ n p} ⊆ {p | IsNGon Γ n p} := by
  rintro d ⟨c, hc, hr | hr⟩
  · exact hc.rotation hr
  · exact hc.reverse.rotation hr

end CFSG.Quasithin.Asc94
