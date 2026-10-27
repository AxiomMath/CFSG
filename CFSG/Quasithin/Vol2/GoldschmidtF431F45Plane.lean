module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Quad

public section

namespace CFSG.Quasithin.H13.F431.F45

open CFSG.Quasithin

universe u v

section Plane

variable {A : Type u} {B : Type v}

structure PPAxioms (r : A → B → Prop) : Prop where
  line_through : ∀ a a', a ≠ a' → ∃ b, r a b ∧ r a' b
  two_pts : ∀ a a' b b', r a b → r a' b → r a b' → r a' b' → a ≠ a' → b = b'
  pt_on : ∀ b b', b ≠ b' → ∃ a, r a b ∧ r a b'
  exB : ∀ b, ∃ a, r a b
  triangle : ∃ (a₀ a₁ a₂ : A) (b₀ b₁ b₂ : B), r a₀ b₀ ∧ r a₁ b₀ ∧ r a₁ b₁ ∧ r a₂ b₁ ∧ r a₂ b₂ ∧
    r a₀ b₂ ∧ a₀ ≠ a₁ ∧ a₁ ≠ a₂ ∧ a₂ ≠ a₀ ∧ b₀ ≠ b₁ ∧ b₁ ≠ b₂ ∧ b₂ ≠ b₀
  thickA : ∀ a, 2 ≤ {b | r a b}.encard
  thickB : ∀ b, 2 ≤ {a | r a b}.encard

variable {r : A → B → Prop}

namespace PPAxioms

variable (h : PPAxioms r)
include h

theorem two_lns {a a' : A} {b b' : B} (h1 : r a b) (h2 : r a' b) (h3 : r a b') (h4 : r a' b')
    (hb : b ≠ b') : a = a' := by
  by_contra hne
  exact hb (h.two_pts a a' b b' h1 h2 h3 h4 hne)

theorem reach (u v : A ⊕ B) : ∃ w : (incGraph r).Walk u v, w.length ≤ 3 := by
  have hAA : ∀ a a' : A, ∃ w : (incGraph r).Walk (.inl a) (.inl a'), w.length ≤ 3 := by
    intro a a'
    by_cases haa : a = a'
    · subst haa
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · obtain ⟨b, hab, hab'⟩ := h.line_through a a' haa
      exact ⟨SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr hab)
        (SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr hab') SimpleGraph.Walk.nil), by simp⟩
  have hBB : ∀ b b' : B, ∃ w : (incGraph r).Walk (.inr b) (.inr b'), w.length ≤ 3 := by
    intro b b'
    by_cases hbb : b = b'
    · subst hbb
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · obtain ⟨a, hab, hab'⟩ := h.pt_on b b' hbb
      exact ⟨SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr hab)
        (SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr hab') SimpleGraph.Walk.nil), by simp⟩
  have hAB : ∀ (a : A) (b : B), ∃ w : (incGraph r).Walk (.inl a) (.inr b), w.length ≤ 3 := by
    intro a b
    by_cases hab : r a b
    · exact ⟨SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr hab) SimpleGraph.Walk.nil,
        by simp⟩
    · obtain ⟨a', ha'⟩ := h.exB b
      have hne : a ≠ a' := fun e => hab (e ▸ ha')
      obtain ⟨b', h1, h2⟩ := h.line_through a a' hne
      exact ⟨SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr h1)
        (SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr h2)
          (SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr ha') SimpleGraph.Walk.nil)),
        by simp⟩
  cases u with
  | inl a =>
    cases v with
    | inl a' => exact hAA a a'
    | inr b => exact hAB a b
  | inr b =>
    cases v with
    | inl a =>
      obtain ⟨w, hw⟩ := hAB a b
      exact ⟨w.reverse, by rw [SimpleGraph.Walk.length_reverse]; exact hw⟩
    | inr b' => exact hBB b b'

theorem connected : (incGraph r).Connected := by
  obtain ⟨a₀, -⟩ := h.triangle
  have : Nonempty (A ⊕ B) := ⟨.inl a₀⟩
  exact ⟨fun u v => (h.reach u v).choose.reachable⟩

theorem dist_le (u v : A ⊕ B) : (incGraph r).dist u v ≤ 3 :=
  (SimpleGraph.dist_le (h.reach u v).choose).trans (h.reach u v).choose_spec

theorem u2 {x y z z' : A ⊕ B} (hxz : (incGraph r).Adj x z) (hzy : (incGraph r).Adj z y)
    (hxz' : (incGraph r).Adj x z') (hz'y : (incGraph r).Adj z' y) (hxy : x ≠ y) : z = z' := by
  cases x with
  | inl a =>
    obtain ⟨b, rfl, hab⟩ := incGraph_adj_inl hxz
    obtain ⟨b', rfl, hab'⟩ := incGraph_adj_inl hxz'
    obtain ⟨a₁, rfl, ha₁b⟩ := incGraph_adj_inr hzy
    obtain ⟨a₂, h2, ha₂b'⟩ := incGraph_adj_inr hz'y
    have e : a₁ = a₂ := Sum.inl.inj h2
    subst e
    have hne : a ≠ a₁ := fun hh => hxy (by rw [hh])
    exact congrArg Sum.inr (h.two_pts a a₁ b b' hab ha₁b hab' ha₂b' hne)
  | inr b =>
    obtain ⟨a, rfl, hab⟩ := incGraph_adj_inr hxz
    obtain ⟨a', rfl, hab'⟩ := incGraph_adj_inr hxz'
    obtain ⟨b₁, rfl, hab₁⟩ := incGraph_adj_inl hzy
    obtain ⟨b₂, h2, hab₂⟩ := incGraph_adj_inl hz'y
    have e : b₁ = b₂ := Sum.inr.inj h2
    subst e
    have hne : b ≠ b₁ := fun hh => hxy (by rw [hh])
    exact congrArg Sum.inl (h.two_lns hab hab' hab₁ hab₂ hne)

theorem uniqueGeod : UniqueGeod (incGraph r) 3 := by
  intro n p q hp hq h0 hn hlt
  have hp' : (incGraph r).dist (p 0) (p n) = n := hp
  interval_cases n
  · exact GPath.ext' fun i hi => by
      have : i = 0 := by omega
      subst this
      exact h0
  · refine GPath.ext' fun i hi => ?_
    interval_cases i
    · exact h0
    · exact hn
  · have hne : p 0 ≠ p 2 := fun e => by
      rw [e, SimpleGraph.dist_self] at hp'
      omega
    have h1 : (incGraph r).Adj (p 0) (p 1) := p.adj 0 (by omega)
    have h2 : (incGraph r).Adj (p 1) (p 2) := p.adj 1 (by omega)
    have h1' : (incGraph r).Adj (p 0) (q 1) := by
      have := q.adj 0 (by omega)
      rwa [← h0] at this
    have h2' : (incGraph r).Adj (q 1) (p 2) := by
      have := q.adj 1 (by omega)
      rwa [← hn] at this
    have e := h.u2 h1 h2 h1' h2' hne
    refine GPath.ext' fun i hi => ?_
    interval_cases i
    · exact h0
    · exact e
    · exact hn

theorem dist_even_of_same {u v : A ⊕ B} (hs : Sum.isLeft u = Sum.isLeft v) :
    Even ((incGraph r).dist u v) :=
  (GPath.dist_even_iff h.connected incGraph_bipartite u v).mp hs

theorem dist_odd_of_ne {u v : A ⊕ B} (hs : Sum.isLeft u ≠ Sum.isLeft v) :
    ¬ Even ((incGraph r).dist u v) := fun he =>
  hs ((GPath.dist_even_iff h.connected incGraph_bipartite u v).mpr he)

theorem dist_inl_inr_eq_three (a : A) (b : B) :
    (incGraph r).dist (.inl a) (.inr b) = 3 ↔ ¬ r a b := by
  have hd := h.dist_le (.inl a) (.inr b)
  have hodd := h.dist_odd_of_ne (u := (.inl a : A ⊕ B)) (v := .inr b) (by simp)
  have h1 : (incGraph r).dist (.inl a) (.inr b) = 1 ↔ r a b :=
    SimpleGraph.dist_eq_one_iff_adj.trans incGraph_adj_inl_inr
  rw [← h1]
  have h0 : (incGraph r).dist (.inl a) (.inr b) ≠ 0 := by
    intro h0
    rw [h0] at hodd
    exact hodd (by decide)
  have h2 : (incGraph r).dist (.inl a) (.inr b) ≠ 2 := by
    intro h2
    rw [h2] at hodd
    exact hodd (by decide)
  omega

theorem dist_inr_inl_eq_three (b : B) (a : A) :
    (incGraph r).dist (.inr b) (.inl a) = 3 ↔ ¬ r a b := by
  rw [SimpleGraph.dist_comm]
  exact h.dist_inl_inr_eq_three a b

theorem dist_inl_inl_ne_three (a a' : A) : (incGraph r).dist (.inl a) (.inl a') ≠ 3 := by
  intro h3
  have := h.dist_even_of_same (u := (.inl a : A ⊕ B)) (v := .inl a') rfl
  rw [h3] at this
  exact absurd this (by decide)

theorem dist_inr_inr_ne_three (b b' : B) : (incGraph r).dist (.inr b) (.inr b') ≠ 3 := by
  intro h3
  have := h.dist_even_of_same (u := (.inr b : A ⊕ B)) (v := .inr b') rfl
  rw [h3] at this
  exact absurd this (by decide)

@[expose] def hexSeq (a₀ a₁ a₂ : A) (b₀ b₁ b₂ : B) (i : ℕ) : A ⊕ B :=
  match i % 6 with
  | 0 => .inl a₀
  | 1 => .inr b₀
  | 2 => .inl a₁
  | 3 => .inr b₁
  | 4 => .inl a₂
  | _ => .inr b₂

end PPAxioms

theorem hexSeq_add (a₀ a₁ a₂ : A) (b₀ b₁ b₂ : B) (i : ℕ) :
    PPAxioms.hexSeq a₀ a₁ a₂ b₀ b₁ b₂ (i + 6) = PPAxioms.hexSeq a₀ a₁ a₂ b₀ b₁ b₂ i := by
  simp [PPAxioms.hexSeq, Nat.add_mod_right]

namespace PPAxioms

variable (h : PPAxioms r)
include h

theorem isGenPolygon : IsGenPolygon (incGraph r) 3 := by
  have hconn := h.connected
  have hc : ∀ a b : A ⊕ B, (incGraph r).Adj a b → Sum.isLeft a ≠ Sum.isLeft b :=
    incGraph_bipartite
  have hU := h.uniqueGeod
  obtain ⟨a₀, a₁, a₂, b₀, b₁, b₂, r00, r10, r11, r21, r22, r02, n01, n12, n20, m01, m12,
    m20⟩ := h.triangle
  have hadj : ∀ i, (incGraph r).Adj (hexSeq a₀ a₁ a₂ b₀ b₁ b₂ i)
      (hexSeq a₀ a₁ a₂ b₀ b₁ b₂ (i + 1)) := by
    intro i
    have hi : i % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have e : (i + 1) % 6 = (i % 6 + 1) % 6 := by omega
    generalize hk : i % 6 = k at hi e
    interval_cases k <;> simp [hexSeq, hk, e] <;>
      first
      | exact r00
      | exact r10
      | exact r11
      | exact r21
      | exact r22
      | exact r02
  have hnb : ∀ i, hexSeq a₀ a₁ a₂ b₀ b₁ b₂ i ≠ hexSeq a₀ a₁ a₂ b₀ b₁ b₂ (i + 2) := by
    intro i
    have hi : i % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have e : (i + 2) % 6 = (i % 6 + 2) % 6 := by omega
    generalize hk : i % 6 = k at hi e
    interval_cases k <;> simp [hexSeq, hk, e] <;>
      first
      | exact n01
      | exact n12
      | exact n20
      | exact m01
      | exact m12
      | exact m20
  have hper : ∀ i, hexSeq a₀ a₁ a₂ b₀ b₁ b₂ (i + 2 * 3) =
      hexSeq a₀ a₁ a₂ b₀ b₁ b₂ i := fun i => hexSeq_add _ _ _ _ _ _ i
  have hnadj : ¬ r a₀ b₁ := fun hr => m01 (h.two_pts a₀ a₁ b₀ b₁ r00 r10 hr r11 n01)
  refine
    { connected := hconn
      bipartite := ⟨Sum.isLeft, hc⟩
      diam_le := h.dist_le
      diam_eq := ⟨.inl a₀, .inr b₁, (h.dist_inl_inr_eq_three a₀ b₁).mpr hnadj⟩
      uniqueGeod := hU
      polygon := ⟨_, GPath.isPolygon_of_periodic hconn hc (by norm_num) hU _ hadj hnb hper⟩
      valence := ?_ }
  intro v
  cases v with
  | inl a =>
    rw [neighborSet_inl, Function.Injective.encard_image Sum.inr_injective]
    exact h.thickA a
  | inr b =>
    rw [neighborSet_inr, Function.Injective.encard_image Sum.inl_injective]
    exact h.thickB b

end PPAxioms

end Plane

end CFSG.Quasithin.H13.F431.F45
