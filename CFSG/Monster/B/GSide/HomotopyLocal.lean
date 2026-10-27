module

public import CFSG.Monster.B.Recog.GenericWalkHomotopy
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.Recog

variable {V : Type*} {G : SimpleGraph V}

theorem elemMove_map {W : Type*} {H : SimpleGraph W} (f : G →g H) {u v : V}
    {p q : G.Walk u v} (h : ElemMove p q) : ElemMove (p.map f) (q.map f) := by
  cases h with
  | backtrack p q h =>
    rw [Walk.map_append, Walk.map_append, Walk.map_cons, Walk.map_cons]
    exact .backtrack _ _ _
  | triangle p q hxy hyz hzx =>
    rw [Walk.map_append, Walk.map_append, Walk.map_cons, Walk.map_cons, Walk.map_cons]
    exact .triangle _ _ _ _ _

theorem homotopic_map {W : Type*} {H : SimpleGraph W} (f : G →g H) {u v : V}
    {p q : G.Walk u v} (h : Homotopic p q) : Homotopic (p.map f) (q.map f) := by
  induction h with
  | rel p q h => exact (elemMove_map f h).homotopic
  | refl p => exact Homotopic.refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem homotopic_of_map_self (k : G →g G) (hk : ∀ x, k x = x) {u v : V}
    {p q : G.Walk u v} (h : Homotopic (p.map k) (q.map k)) : Homotopic p q := by
  obtain rfl : k = Hom.id := RelHom.ext hk
  rwa [Walk.map_id, Walk.map_id] at h

theorem homotopic_of_map {W : Type*} {H : SimpleGraph W} (f : G →g H) (g : H →g G)
    (hgf : ∀ x, g (f x) = x) {u v : V} {p q : G.Walk u v}
    (h : Homotopic (p.map f) (q.map f)) : Homotopic p q := by
  have h' := homotopic_map g h
  rw [Walk.map_map, Walk.map_map] at h'
  exact homotopic_of_map_self (g.comp f) hgf h'

theorem triangulable_iff_of_iso {W : Type*} {H : SimpleGraph W} (e : G ≃g H) :
    Triangulable G ↔ Triangulable H :=
  ⟨fun hG _ _ => homotopic_of_map e.symm.toHom e.toHom (fun x => e.apply_symm_apply x) (hG _ _),
    fun hH _ _ => homotopic_of_map e.toHom e.symm.toHom (fun x => e.symm_apply_apply x)
      (hH _ _)⟩

theorem homotopic_copy {u v u' v' : V} {p q : G.Walk u v} (h : Homotopic p q) (hu : u = u')
    (hv : v = v') : Homotopic (p.copy hu hv) (q.copy hu hv) := by
  subst hu hv
  exact h

theorem homotopic_iff_append_reverse_nil {u v : V} {p q : G.Walk u v} :
    Homotopic p q ↔ Homotopic (p.append q.reverse) .nil := by
  refine ⟨fun h => (h.append_right q.reverse).trans (homotopic_append_reverse q), fun h => ?_⟩
  have h₁ : Homotopic (p.append (q.reverse.append q)) p := by
    simpa using (homotopic_reverse_append q).append_left p
  have h₂ : Homotopic ((p.append q.reverse).append q) q := by
    simpa using h.append_right q
  rw [← Walk.append_assoc] at h₂
  exact h₁.symm.trans h₂

theorem homotopic_nil_append_comm {u v : V} (p : G.Walk u v) (q : G.Walk v u) :
    Homotopic (p.append q) .nil ↔ Homotopic (q.append p) .nil := by
  suffices key : ∀ {u v : V} (p : G.Walk u v) (q : G.Walk v u),
      Homotopic (p.append q) .nil → Homotopic (q.append p) .nil from ⟨key p q, key q p⟩
  intro u v p q h
  have h₁ := (homotopic_append_reverse q).append_left (q.append p)
  rw [Walk.append_nil] at h₁
  have h₂ := (h.append_right q.reverse).append_left q
  rw [Walk.nil_append] at h₂
  have e : (q.append p).append (q.append q.reverse) =
      q.append ((p.append q).append q.reverse) := by
    simp only [Walk.append_assoc]
  rw [e] at h₁
  exact h₁.symm.trans (h₂.trans (homotopic_append_reverse q))

theorem homotopic_triangle_nil {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hzx : G.Adj z x) : Homotopic (.cons hxy (.cons hyz (.cons hzx .nil)) : G.Walk x x) .nil :=
  (homotopic_triangle (.nil : G.Walk x x) .nil hxy hyz hzx).symm

theorem homotopic_nil_of_length_le_three {u : V} (p : G.Walk u u) (hp : p.length ≤ 3) :
    Homotopic p .nil := by
  match u, p, hp with
  | _, .nil, _ => exact Homotopic.refl _
  | _, .cons h .nil, _ => exact absurd h (G.loopless.irrefl _)
  | _, .cons h₁ (.cons _ .nil), _ => exact homotopic_cons_cons_nil h₁
  | _, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ => exact homotopic_triangle_nil h₁ h₂ h₃
  | _, .cons _ (.cons _ (.cons _ (.cons _ _))), hp =>
    simp only [Walk.length_cons] at hp
    omega

theorem homotopic_edge_triangle {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hxz : G.Adj x z) : Homotopic (.cons hxz .nil : G.Walk x z) (.cons hxy (.cons hyz .nil)) :=
  homotopic_iff_append_reverse_nil.2 (homotopic_nil_of_length_le_three _ (by simp))

theorem homotopic_cone_spokes {z u v : V} (p : G.Walk u v)
    (hz : ∀ x ∈ p.support, x = z ∨ G.Adj x z) (s : G.Walk z u) (hs : s.length ≤ 1)
    (t : G.Walk z v) (ht : t.length ≤ 1) : Homotopic p (s.reverse.append t) := by
  induction p with
  | nil =>
    obtain rfl : s = t := Walk.eq_of_length_le_one hs ht
    exact (homotopic_reverse_append s).symm
  | @cons a w b h p ih =>
    obtain ⟨s', hs'⟩ : ∃ s' : G.Walk z w, s'.length ≤ 1 := by
      rcases hz w (by simp) with rfl | hw
      · exact ⟨.nil, by simp⟩
      · exact ⟨.cons hw.symm .nil, by simp⟩
    have ih' := ih (fun x hx => hz x (by simp [hx])) s' hs' t ht
    have hc : Homotopic (.cons h s'.reverse) s.reverse :=
      homotopic_iff_append_reverse_nil.2
        (homotopic_nil_of_length_le_three _ (by simp; omega))
    have h₂ := hc.append_right t
    rw [Walk.cons_append] at h₂
    exact (ih'.cons h).trans h₂

theorem homotopic_cone {z u v : V} (p : G.Walk u v) (hz : ∀ x ∈ p.support, G.Adj x z) :
    Homotopic p (.cons (hz u p.start_mem_support) (.cons (hz v p.end_mem_support).symm .nil)) :=
  homotopic_cone_spokes p (fun x hx => Or.inr (hz x hx))
    (.cons (hz u p.start_mem_support).symm .nil) (by simp)
    (.cons (hz v p.end_mem_support).symm .nil) (by simp)

theorem homotopic_nil_of_forall_adj_or_eq {z u : V} (p : G.Walk u u)
    (hz : ∀ x ∈ p.support, x = z ∨ G.Adj x z) : Homotopic p .nil := by
  obtain ⟨s, hs⟩ : ∃ s : G.Walk z u, s.length ≤ 1 := by
    rcases hz u p.start_mem_support with rfl | hu
    · exact ⟨.nil, by simp⟩
    · exact ⟨.cons hu.symm .nil, by simp⟩
  exact (homotopic_cone_spokes p hz s hs s hs).trans (homotopic_reverse_append s)

theorem homotopic_nil_of_forall_adj {z u : V} (p : G.Walk u u)
    (hz : ∀ x ∈ p.support, G.Adj x z) : Homotopic p .nil :=
  homotopic_nil_of_forall_adj_or_eq p fun x hx => Or.inr (hz x hx)

private theorem homotopic_path_two_step {a c y₁ y₂ : V} (h₁ : G.Adj a y₁) (h₂ : G.Adj y₁ c)
    (h₃ : G.Adj a y₂) (h₄ : G.Adj y₂ c) (h : G.Adj y₁ y₂) :
    Homotopic (.cons h₁ (.cons h₂ .nil) : G.Walk a c) (.cons h₃ (.cons h₄ .nil)) :=
  ((homotopic_edge_triangle h₃ h.symm h₁).append_right (.cons h₂ .nil)).trans
    ((homotopic_edge_triangle h.symm h₂ h₄).symm.cons h₃)

private theorem homotopic_path_two_of_walk {a c : V} {y₁ y₂ : G.commonNeighbors a c}
    (w : (G.induce (G.commonNeighbors a c)).Walk y₁ y₂) :
    Homotopic (.cons (G.mem_commonNeighbors.1 y₁.2).1
        (.cons (G.mem_commonNeighbors.1 y₁.2).2.symm .nil) : G.Walk a c)
      (.cons (G.mem_commonNeighbors.1 y₂.2).1
        (.cons (G.mem_commonNeighbors.1 y₂.2).2.symm .nil)) := by
  induction w with
  | nil => exact Homotopic.refl _
  | @cons y₁ y₂ _ h _ ih =>
    exact (homotopic_path_two_step (G.mem_commonNeighbors.1 y₁.2).1
      (G.mem_commonNeighbors.1 y₁.2).2.symm (G.mem_commonNeighbors.1 y₂.2).1
      (G.mem_commonNeighbors.1 y₂.2).2.symm (SimpleGraph.induce_adj.1 h)).trans ih

theorem homotopic_path_two_of_reachable {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (had : G.Adj a d) (hdc : G.Adj d c)
    (hr : (G.induce (G.commonNeighbors a c)).Reachable
      ⟨b, G.mem_commonNeighbors.2 ⟨hab, hbc.symm⟩⟩ ⟨d, G.mem_commonNeighbors.2 ⟨had, hdc.symm⟩⟩) :
    Homotopic (.cons hab (.cons hbc .nil) : G.Walk a c) (.cons had (.cons hdc .nil)) := by
  obtain ⟨w⟩ := hr
  exact homotopic_path_two_of_walk w

theorem homotopic_quadrangle_nil {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a)
    (hr : (G.induce (G.commonNeighbors a c)).Reachable
      ⟨b, G.mem_commonNeighbors.2 ⟨hab, hbc.symm⟩⟩ ⟨d, G.mem_commonNeighbors.2 ⟨hda.symm, hcd⟩⟩) :
    Homotopic (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a) .nil :=
  homotopic_iff_append_reverse_nil.1 (homotopic_path_two_of_reachable hab hbc hda.symm hcd.symm hr)

theorem homotopic_quadrangle_nil_of_preconnected {a c : V}
    (hμ : (G.induce (G.commonNeighbors a c)).Preconnected) {b d : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    Homotopic (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a) .nil :=
  homotopic_quadrangle_nil hab hbc hcd hda (hμ _ _)

end CFSG.Monster.B.GSide
