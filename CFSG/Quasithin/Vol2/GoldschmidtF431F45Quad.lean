module

public import CFSG.Quasithin.Recognition.F4Basic

public section

namespace CFSG.Quasithin.H13.F431.F45

open CFSG.Quasithin

universe u v

section Graph

variable {A : Type u} {B : Type v}

@[expose] def incGraph (r : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj
    | .inl a, .inr b => r a b
    | .inr b, .inl a => r a b
    | _, _ => False
  symm := ⟨by
    intro u w h
    cases u <;> cases w <;> exact h⟩
  loopless := ⟨by
    intro u h
    cases u <;> exact h⟩

variable {r : A → B → Prop}

theorem incGraph_adj_inl_inr {a : A} {b : B} : (incGraph r).Adj (.inl a) (.inr b) ↔ r a b :=
  Iff.rfl

theorem incGraph_adj_inr_inl {a : A} {b : B} : (incGraph r).Adj (.inr b) (.inl a) ↔ r a b :=
  Iff.rfl

theorem incGraph_adj_inl {a : A} {w : A ⊕ B} (h : (incGraph r).Adj (.inl a) w) :
    ∃ b, w = .inr b ∧ r a b := by
  cases w with
  | inl a' => exact False.elim h
  | inr b => exact ⟨b, rfl, h⟩

theorem incGraph_adj_inr {b : B} {w : A ⊕ B} (h : (incGraph r).Adj (.inr b) w) :
    ∃ a, w = .inl a ∧ r a b := by
  cases w with
  | inl a => exact ⟨a, rfl, h⟩
  | inr b' => exact False.elim h

theorem incGraph_bipartite (a b : A ⊕ B) (h : (incGraph r).Adj a b) :
    Sum.isLeft a ≠ Sum.isLeft b := by
  cases a <;> cases b <;> first | exact False.elim h | simp

structure GQAxioms (r : A → B → Prop) : Prop where
  exA : ∀ a, ∃ b, r a b
  exB : ∀ b, ∃ a, r a b
  two_pts : ∀ a a' b b', r a b → r a' b → r a b' → r a' b' → a ≠ a' → b = b'
  ax2 : ∀ a b, ¬ r a b → ∃ a' b', r a b' ∧ r a' b' ∧ r a' b
  no_triangle : ∀ a₀ a₁ a₂ b₀ b₁ b₂, r a₀ b₀ → r a₁ b₀ → r a₁ b₁ → r a₂ b₁ → r a₂ b₂ → r a₀ b₂ →
    a₀ ≠ a₁ → a₁ ≠ a₂ → a₂ ≠ a₀ → b₀ ≠ b₁ → False
  octagon : ∃ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃, r a₀ b₀ ∧ r a₁ b₀ ∧ r a₁ b₁ ∧ r a₂ b₁ ∧ r a₂ b₂ ∧
    r a₃ b₂ ∧ r a₃ b₃ ∧ r a₀ b₃ ∧ a₀ ≠ a₁ ∧ a₁ ≠ a₂ ∧ a₂ ≠ a₃ ∧ a₃ ≠ a₀ ∧ b₀ ≠ b₁ ∧ b₁ ≠ b₂ ∧
    b₂ ≠ b₃ ∧ b₃ ≠ b₀
  thickA : ∀ a, 2 ≤ {b | r a b}.encard
  thickB : ∀ b, 2 ≤ {a | r a b}.encard

namespace GQAxioms

variable (h : GQAxioms r)
include h

theorem two_lns {a a' : A} {b b' : B} (h1 : r a b) (h2 : r a' b) (h3 : r a b') (h4 : r a' b')
    (hb : b ≠ b') : a = a' := by
  by_contra hne
  exact hb (h.two_pts a a' b b' h1 h2 h3 h4 hne)

theorem reach (u v : A ⊕ B) : ∃ w : (incGraph r).Walk u v, w.length ≤ 4 := by
  have hAA : ∀ a a' : A, ∃ w : (incGraph r).Walk (.inl a) (.inl a'), w.length ≤ 4 := by
    intro a a'
    by_cases haa : a = a'
    · subst haa
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
    by_cases hc : ∃ b, r a b ∧ r a' b
    · obtain ⟨b, hab, hab'⟩ := hc
      exact ⟨SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr hab)
        (SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr hab') SimpleGraph.Walk.nil), by simp⟩
    · obtain ⟨b', hb'⟩ := h.exA a'
      have hn : ¬ r a b' := fun hh => hc ⟨b', hh, hb'⟩
      obtain ⟨a'', b'', h1, h2, h3⟩ := h.ax2 a b' hn
      exact ⟨SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr h1)
        (SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr h2)
          (SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr h3)
            (SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr hb') SimpleGraph.Walk.nil))),
        by simp⟩
  have hAB : ∀ (a : A) (b : B), ∃ w : (incGraph r).Walk (.inl a) (.inr b), w.length ≤ 3 := by
    intro a b
    by_cases hab : r a b
    · exact ⟨SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr hab) SimpleGraph.Walk.nil,
        by simp⟩
    · obtain ⟨a', b', h1, h2, h3⟩ := h.ax2 a b hab
      exact ⟨SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr h1)
        (SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr h2)
          (SimpleGraph.Walk.cons (incGraph_adj_inl_inr.mpr h3) SimpleGraph.Walk.nil)),
        by simp⟩
  cases u with
  | inl a =>
    cases v with
    | inl a' => exact hAA a a'
    | inr b =>
      obtain ⟨w, hw⟩ := hAB a b
      exact ⟨w, by omega⟩
  | inr b =>
    cases v with
    | inl a =>
      obtain ⟨w, hw⟩ := hAB a b
      exact ⟨w.reverse, by rw [SimpleGraph.Walk.length_reverse]; omega⟩
    | inr b' =>
      obtain ⟨a, ha⟩ := h.exB b
      obtain ⟨w, hw⟩ := hAB a b'
      exact ⟨SimpleGraph.Walk.cons (incGraph_adj_inr_inl.mpr ha) w, by
        rw [SimpleGraph.Walk.length_cons]; omega⟩

theorem connected : (incGraph r).Connected := by
  obtain ⟨a₀, -⟩ := h.octagon
  have : Nonempty (A ⊕ B) := ⟨.inl a₀⟩
  exact ⟨fun u v => (h.reach u v).choose.reachable⟩

theorem dist_le (u v : A ⊕ B) : (incGraph r).dist u v ≤ 4 :=
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

theorem u3 {x y v₁ v₂ v₁' v₂' : A ⊕ B} (h1 : (incGraph r).Adj x v₁) (h2 : (incGraph r).Adj v₁ v₂)
    (h3 : (incGraph r).Adj v₂ y) (h1' : (incGraph r).Adj x v₁') (h2' : (incGraph r).Adj v₁' v₂')
    (h3' : (incGraph r).Adj v₂' y) (hxy : ¬ (incGraph r).Adj x y) : v₁ = v₁' ∧ v₂ = v₂' := by
  cases x with
  | inl a₀ =>
    obtain ⟨b₁, rfl, hab₁⟩ := incGraph_adj_inl h1
    obtain ⟨b₁', rfl, hab₁'⟩ := incGraph_adj_inl h1'
    obtain ⟨a₂, rfl, ha₂b₁⟩ := incGraph_adj_inr h2
    obtain ⟨a₂', rfl, ha₂'b₁'⟩ := incGraph_adj_inr h2'
    obtain ⟨b₃, rfl, ha₂b₃⟩ := incGraph_adj_inl h3
    obtain ⟨b₃', hb, ha₂'b₃'⟩ := incGraph_adj_inl h3'
    have e : b₃ = b₃' := Sum.inr.inj hb
    subst e
    have hn : ¬ r a₀ b₃ := hxy
    have ha02 : a₀ ≠ a₂ := fun e => hn (e ▸ ha₂b₃)
    have ha02' : a₀ ≠ a₂' := fun e => hn (e ▸ ha₂'b₃')
    have hb13 : b₁ ≠ b₃ := fun e => hn (e ▸ hab₁)
    have hbb : a₂ = a₂' := by
      by_contra hne
      exact h.no_triangle a₀ a₂ a₂' b₁ b₃ b₁' hab₁ ha₂b₁ ha₂b₃ ha₂'b₃' ha₂'b₁' hab₁' ha02 hne
        (Ne.symm ha02') hb13
    subst hbb
    have : b₁ = b₁' := h.two_pts a₀ a₂ b₁ b₁' hab₁ ha₂b₁ hab₁' ha₂'b₁' ha02
    subst this
    exact ⟨rfl, rfl⟩
  | inr b₀ =>
    obtain ⟨a₁, rfl, ha₁b₀⟩ := incGraph_adj_inr h1
    obtain ⟨a₁', rfl, ha₁'b₀⟩ := incGraph_adj_inr h1'
    obtain ⟨b₂, rfl, ha₁b₂⟩ := incGraph_adj_inl h2
    obtain ⟨b₂', rfl, ha₁'b₂'⟩ := incGraph_adj_inl h2'
    obtain ⟨a₃, rfl, ha₃b₂⟩ := incGraph_adj_inr h3
    obtain ⟨a₃', hb, ha₃'b₂'⟩ := incGraph_adj_inr h3'
    have e : a₃ = a₃' := Sum.inl.inj hb
    subst e
    have hn : ¬ r a₃ b₀ := hxy
    have h13 : a₁ ≠ a₃ := fun e => hn (e ▸ ha₁b₀)
    have h13' : a₁' ≠ a₃ := fun e => hn (e ▸ ha₁'b₀)
    have hb02 : b₀ ≠ b₂ := fun e => hn (e ▸ ha₃b₂)
    have hbb : b₂ = b₂' := by
      by_contra hne
      have ha : a₁ ≠ a₁' := fun e =>
        hne (h.two_pts a₁ a₃ b₂ b₂' ha₁b₂ ha₃b₂ (e ▸ ha₁'b₂') ha₃'b₂' h13)
      exact h.no_triangle a₁ a₃ a₁' b₂ b₂' b₀ ha₁b₂ ha₃b₂ ha₃'b₂' ha₁'b₂' ha₁'b₀ ha₁b₀ h13
        (Ne.symm h13') (Ne.symm ha) hne
    subst hbb
    have : a₁ = a₁' := h.two_lns ha₁b₀ ha₁'b₀ ha₁b₂ ha₁'b₂' hb02
    subst this
    exact ⟨rfl, rfl⟩

theorem uniqueGeod : UniqueGeod (incGraph r) 4 := by
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
  · have hxy : ¬ (incGraph r).Adj (p 0) (p 3) := fun hadj => by
      have := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      omega
    have h1 : (incGraph r).Adj (p 0) (p 1) := p.adj 0 (by omega)
    have h2 : (incGraph r).Adj (p 1) (p 2) := p.adj 1 (by omega)
    have h3 : (incGraph r).Adj (p 2) (p 3) := p.adj 2 (by omega)
    have h1' : (incGraph r).Adj (p 0) (q 1) := by
      have := q.adj 0 (by omega)
      rwa [← h0] at this
    have h2' : (incGraph r).Adj (q 1) (q 2) := q.adj 1 (by omega)
    have h3' : (incGraph r).Adj (q 2) (p 3) := by
      have := q.adj 2 (by omega)
      rwa [← hn] at this
    obtain ⟨e1, e2⟩ := h.u3 h1 h2 h3 h1' h2' h3' hxy
    refine GPath.ext' fun i hi => ?_
    interval_cases i
    · exact h0
    · exact e1
    · exact e2
    · exact hn

end GQAxioms

@[expose] def octSeq (a₀ a₁ a₂ a₃ : A) (b₀ b₁ b₂ b₃ : B) (i : ℕ) : A ⊕ B :=
  match i % 8 with
  | 0 => .inl a₀
  | 1 => .inr b₀
  | 2 => .inl a₁
  | 3 => .inr b₁
  | 4 => .inl a₂
  | 5 => .inr b₂
  | 6 => .inl a₃
  | _ => .inr b₃

theorem octSeq_add (a₀ a₁ a₂ a₃ : A) (b₀ b₁ b₂ b₃ : B) (i : ℕ) :
    octSeq a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ (i + 8) = octSeq a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ i := by
  simp [octSeq, Nat.add_mod_right]

theorem neighborSet_inl (a : A) :
    (incGraph r).neighborSet (.inl a) = Sum.inr '' {b | r a b} := by
  ext w
  constructor
  · intro hw
    obtain ⟨b, rfl, hb⟩ := incGraph_adj_inl hw
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact hb

theorem neighborSet_inr (b : B) :
    (incGraph r).neighborSet (.inr b) = Sum.inl '' {a | r a b} := by
  ext w
  constructor
  · intro hw
    obtain ⟨a, rfl, ha⟩ := incGraph_adj_inr hw
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ha

namespace GQAxioms

variable (h : GQAxioms r)
include h

theorem isGenPolygon : IsGenPolygon (incGraph r) 4 := by
  have hconn := h.connected
  have hc : ∀ a b : A ⊕ B, (incGraph r).Adj a b → Sum.isLeft a ≠ Sum.isLeft b :=
    incGraph_bipartite
  have hU := h.uniqueGeod
  obtain ⟨a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃, r00, r10, r11, r21, r22, r32, r33, r03, n01, n12, n23,
    n30, m01, m12, m23, m30⟩ := h.octagon
  have hadj : ∀ i, (incGraph r).Adj (octSeq a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ i)
      (octSeq a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ (i + 1)) := by
    intro i
    have hi : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have e : (i + 1) % 8 = (i % 8 + 1) % 8 := by omega
    generalize hk : i % 8 = k at hi e
    interval_cases k <;> simp [octSeq, hk, e] <;>
      first
      | exact r00
      | exact r10
      | exact r11
      | exact r21
      | exact r22
      | exact r32
      | exact r33
      | exact r03
  have hnb : ∀ i, octSeq a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ i ≠ octSeq a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ (i + 2) := by
    intro i
    have hi : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have e : (i + 2) % 8 = (i % 8 + 2) % 8 := by omega
    generalize hk : i % 8 = k at hi e
    interval_cases k <;> simp [octSeq, hk, e] <;>
      first
      | exact n01
      | exact n12
      | exact n23
      | exact n30
      | exact m01
      | exact m12
      | exact m23
      | exact m30
  have hper : ∀ i, octSeq a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ (i + 2 * 4) =
      octSeq a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ i := fun i => octSeq_add _ _ _ _ _ _ _ _ i
  refine
    { connected := hconn
      bipartite := ⟨Sum.isLeft, hc⟩
      diam_le := h.dist_le
      diam_eq := ⟨octSeq a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ 0, octSeq a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ 4, ?_⟩
      uniqueGeod := hU
      polygon := ⟨_, GPath.isPolygon_of_periodic hconn hc (by norm_num) hU _ hadj hnb hper⟩
      valence := ?_ }
  · have := GPath.window_dist hconn hc hU _ hadj hnb 0 (le_refl 4)
    simpa using this
  · intro v
    cases v with
    | inl a =>
      rw [neighborSet_inl, Function.Injective.encard_image Sum.inr_injective]
      exact h.thickA a
    | inr b =>
      rw [neighborSet_inr, Function.Injective.encard_image Sum.inl_injective]
      exact h.thickB b

end GQAxioms

namespace GQAxioms

variable (h : GQAxioms r)
include h

theorem dist_even_of_same {u v : A ⊕ B} (hs : Sum.isLeft u = Sum.isLeft v) :
    Even ((incGraph r).dist u v) :=
  (GPath.dist_even_iff h.connected incGraph_bipartite u v).mp hs

theorem dist_odd_of_ne {u v : A ⊕ B} (hs : Sum.isLeft u ≠ Sum.isLeft v) :
    ¬ Even ((incGraph r).dist u v) := fun he =>
  hs ((GPath.dist_even_iff h.connected incGraph_bipartite u v).mpr he)

theorem two_lt_dist_iff (u v : A ⊕ B) : 2 < (incGraph r).dist u v ↔
    u ≠ v ∧ ¬ (incGraph r).Adj u v ∧ (incGraph r).commonNeighbors u v = ∅ := by
  rw [← SimpleGraph.two_lt_edist_iff, ← (h.connected.preconnected u v).coe_dist_eq_edist]
  exact_mod_cast Iff.rfl

theorem dist_inl_inl_eq_four (a a' : A) :
    (incGraph r).dist (.inl a) (.inl a') = 4 ↔ a ≠ a' ∧ ¬ ∃ b, r a b ∧ r a' b := by
  have hd := h.dist_le (.inl a) (.inl a')
  obtain ⟨k, hk⟩ := h.dist_even_of_same (u := (.inl a : A ⊕ B)) (v := .inl a') rfl
  have h4 : (incGraph r).dist (.inl a) (.inl a') = 4 ↔
      2 < (incGraph r).dist (.inl a) (.inl a') := by
    omega
  rw [h4, h.two_lt_dist_iff]
  constructor
  · rintro ⟨hne, -, hcn⟩
    refine ⟨fun hh => hne (by rw [hh]), ?_⟩
    rintro ⟨b, h1, h2⟩
    have : (.inr b : A ⊕ B) ∈ (incGraph r).commonNeighbors (.inl a) (.inl a') := ⟨h1, h2⟩
    rw [hcn] at this
    exact this
  · rintro ⟨hne, hno⟩
    refine ⟨fun hh => hne (Sum.inl.inj hh), fun hh => hh, ?_⟩
    ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    cases w with
    | inl a'' => exact hw.1
    | inr b => exact hno ⟨b, hw.1, hw.2⟩

theorem dist_inr_inr_eq_four (b b' : B) :
    (incGraph r).dist (.inr b) (.inr b') = 4 ↔ b ≠ b' ∧ ¬ ∃ a, r a b ∧ r a b' := by
  have hd := h.dist_le (.inr b) (.inr b')
  obtain ⟨k, hk⟩ := h.dist_even_of_same (u := (.inr b : A ⊕ B)) (v := .inr b') rfl
  have h4 : (incGraph r).dist (.inr b) (.inr b') = 4 ↔
      2 < (incGraph r).dist (.inr b) (.inr b') := by
    omega
  rw [h4, h.two_lt_dist_iff]
  constructor
  · rintro ⟨hne, -, hcn⟩
    refine ⟨fun hh => hne (by rw [hh]), ?_⟩
    rintro ⟨a, h1, h2⟩
    have : (.inl a : A ⊕ B) ∈ (incGraph r).commonNeighbors (.inr b) (.inr b') := ⟨h1, h2⟩
    rw [hcn] at this
    exact this
  · rintro ⟨hne, hno⟩
    refine ⟨fun hh => hne (Sum.inr.inj hh), fun hh => hh, ?_⟩
    ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    cases w with
    | inl a => exact hno ⟨a, hw.1, hw.2⟩
    | inr b'' => exact hw.1

theorem dist_inl_inr_ne_four (a : A) (b : B) : (incGraph r).dist (.inl a) (.inr b) ≠ 4 := by
  intro h4
  have := h.dist_odd_of_ne (u := (.inl a : A ⊕ B)) (v := .inr b) (by simp)
  exact this (by rw [h4]; decide)

theorem dist_inr_inl_ne_four (b : B) (a : A) : (incGraph r).dist (.inr b) (.inl a) ≠ 4 := by
  intro h4
  have := h.dist_odd_of_ne (u := (.inr b : A ⊕ B)) (v := .inl a) (by simp)
  exact this (by rw [h4]; decide)

end GQAxioms

end Graph

end CFSG.Quasithin.H13.F431.F45
