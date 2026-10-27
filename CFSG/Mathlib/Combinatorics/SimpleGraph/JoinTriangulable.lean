module

public import CFSG.Monster.B.Recog.GenericShortCycles
import CFSG.Monster.B.GSide.HomotopyLocal
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public section

namespace CFSG.Combinatorics

open SimpleGraph CFSG.Monster.B.Recog CFSG.Monster.B.GSide

variable {V ι : Type*} {G : SimpleGraph V}

theorem triangulable_of_lasso {b : V} (γ : ∀ x, G.Walk b x)
    (hγ : ∀ x y (h : G.Adj x y), Homotopic (lasso γ h) .nil) : Triangulable G := by
  intro u p
  obtain ⟨L, hL, hp⟩ := homotopic_foldr_lasso γ p
  have hnull : Homotopic ((γ u).append (p.append (γ u).reverse)) .nil :=
    hp.trans (homotopic_walkProd_nil fun q hq => by
      obtain ⟨x, y, h, rfl⟩ := hL q hq
      exact hγ x y h)
  have h₁ := (homotopic_nil_append_comm _ _).1 hnull
  rw [← Walk.append_assoc] at h₁
  have h₂ : Homotopic (p.append ((γ u).reverse.append (γ u))) p := by
    simpa using (homotopic_reverse_append (γ u)).append_left p
  exact h₂.symm.trans h₁

theorem mem_support_lasso {b : V} (γ : ∀ x, G.Walk b x) {x y v : V} (h : G.Adj x y)
    (hv : v ∈ (lasso γ h).support) : v ∈ (γ x).support ∨ v ∈ (γ y).support := by
  simp only [lasso, Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons,
    Walk.support_reverse, List.mem_reverse] at hv
  rcases hv with hv | rfl | hv
  · exact Or.inl hv
  · exact Or.inl (Walk.end_mem_support _)
  · exact Or.inr hv

section Join

variable (part : V → ι) (hadj : ∀ x y, part x ≠ part y → G.Adj x y)

include hadj in
theorem homotopic_nil_of_part {z u : V} (p : G.Walk u u)
    (hz : ∀ v ∈ p.support, v = z ∨ part v ≠ part z) : Homotopic p .nil :=
  homotopic_nil_of_forall_adj_or_eq p fun v hv => (hz v hv).imp_right (hadj v z)

@[expose] def joinWalk [DecidableEq ι] {a b : V} (hab : part a ≠ part b) (x : V) : G.Walk a x :=
  if h : part a = part x then
    .cons (hadj a b hab) (.cons (hadj b x fun e => hab (h.trans e.symm)) .nil)
  else .cons (hadj a x h) .nil

theorem joinWalk_of_eq [DecidableEq ι] {a b x : V} (hab : part a ≠ part b) (h : part a = part x) :
    joinWalk part hadj hab x =
      .cons (hadj a b hab) (.cons (hadj b x fun e => hab (h.trans e.symm)) .nil) :=
  dif_pos h

theorem joinWalk_of_ne [DecidableEq ι] {a b x : V} (hab : part a ≠ part b) (h : part a ≠ part x) :
    joinWalk part hadj hab x = .cons (hadj a x h) .nil :=
  dif_neg h

theorem mem_support_joinWalk [DecidableEq ι] {a b x v : V} (hab : part a ≠ part b)
    (hv : v ∈ (joinWalk part hadj hab x).support) : v = a ∨ v = b ∨ v = x := by
  by_cases h : part a = part x
  · rw [joinWalk_of_eq part hadj hab h] at hv
    simpa using hv
  · rw [joinWalk_of_ne part hadj hab h] at hv
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    tauto

theorem mem_support_lasso_joinWalk [DecidableEq ι] {a b x y v : V} (hab : part a ≠ part b)
    (h : G.Adj x y) (hv : v ∈ (lasso (joinWalk part hadj hab) h).support) :
    v = a ∨ v = b ∨ v = x ∨ v = y := by
  rcases mem_support_lasso _ h hv with hv | hv <;>
    rcases mem_support_joinWalk part hadj hab hv with e | e | e <;> tauto

include hadj in
theorem connected_of_part {a b : V} (hab : part a ≠ part b) : G.Connected := by
  refine (connected_iff_exists_forall_reachable G).2 ⟨a, fun x => ?_⟩
  by_cases hx : part a = part x
  · exact (hadj a b hab).reachable.trans (hadj b x fun e => hab (hx.trans e.symm)).reachable
  · exact (hadj a x hx).reachable

include hadj in
theorem triangulable_of_part_three {a b c : V} (hab : part a ≠ part b) (hbc : part b ≠ part c)
    (hac : part a ≠ part c) : Triangulable G := by
  classical
  refine triangulable_of_lasso (joinWalk part hadj hab) fun x y h => ?_
  obtain ⟨z, hz, hxz, hyz⟩ :
      ∃ z, (z = a ∨ z = b ∨ z = c) ∧ part x ≠ part z ∧ part y ≠ part z := by
    by_cases hxa : part x = part a
    · by_cases hyb : part y = part b
      · exact ⟨c, by simp, fun e => hac (hxa.symm.trans e), fun e => hbc (hyb.symm.trans e)⟩
      · exact ⟨b, by simp, fun e => hab (hxa.symm.trans e), hyb⟩
    · by_cases hya : part y = part a
      · by_cases hxb : part x = part b
        · exact ⟨c, by simp, fun e => hbc (hxb.symm.trans e), fun e => hac (hya.symm.trans e)⟩
        · exact ⟨b, by simp, hxb, fun e => hab (hya.symm.trans e)⟩
      · exact ⟨a, by simp, hxa, hya⟩
  have hza : a = z ∨ part a ≠ part z := by
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hab
    · exact Or.inr hac
  have hzb : b = z ∨ part b ≠ part z := by
    rcases hz with rfl | rfl | rfl
    · exact Or.inr hab.symm
    · exact Or.inl rfl
    · exact Or.inr hbc
  refine homotopic_nil_of_part part hadj (z := z) _ fun v hv => ?_
  rcases mem_support_lasso_joinWalk part hadj hab h hv with e | e | e | e <;> rw [e]
  · exact hza
  · exact hzb
  · exact Or.inr hxz
  · exact Or.inr hyz

include hadj in
theorem triangulable_of_part_connected {i : ι} {b : V} (hb : part b ≠ i)
    (hP : (G.induce {x | part x = i}).Connected) : Triangulable G := by
  classical
  obtain ⟨⟨a, ha⟩⟩ := hP.nonempty
  have ha : part a = i := ha
  have hba : part b ≠ part a := fun e => hb (e.trans ha)
  have hsub : ∀ {u w : V}, part u ≠ i → part w ≠ i →
      {x | part x = i} ⊆ G.commonNeighbors u w := fun hu hw x hx =>
    G.mem_commonNeighbors.2 ⟨hadj _ _ fun e => hu (e.trans hx), hadj _ _ fun e => hw (e.trans hx)⟩
  have hreach : ∀ {u w x x' : V} (hu : part u ≠ i) (hw : part w ≠ i) (hx : part x = i)
      (hx' : part x' = i), (G.induce (G.commonNeighbors u w)).Reachable
        ⟨x, hsub hu hw hx⟩ ⟨x', hsub hu hw hx'⟩ := fun hu hw hx hx' =>
    (hP.preconnected ⟨_, hx⟩ ⟨_, hx'⟩).map (G.induceHomOfLE (hsub hu hw)).toHom
  refine triangulable_of_lasso (joinWalk part hadj hba) fun x y h => ?_
  have hs : ∀ v ∈ (lasso (joinWalk part hadj hba) h).support, v = b ∨ v = a ∨ v = x ∨ v = y :=
    fun v hv => mem_support_lasso_joinWalk part hadj hba h hv
  by_cases hxi : part x = i
  · by_cases hyb : part y = part b
    ·
      rw [lasso, joinWalk_of_ne part hadj hba (fun e => hb (e.trans hxi)),
        joinWalk_of_eq part hadj hba hyb.symm]
      simp only [Walk.reverse_cons, Walk.reverse_nil, Walk.nil_append, Walk.cons_append]
      exact homotopic_quadrangle_nil _ _ _ _
        (hreach hb (fun e => hb (hyb.symm.trans e)) hxi ha)
    ·
      refine homotopic_nil_of_part part hadj (z := b) _ fun v hv => ?_
      rcases hs v hv with e | e | e | e <;> rw [e]
      · exact Or.inl rfl
      · exact Or.inr hba.symm
      · exact Or.inr fun e => hb (e.symm.trans hxi)
      · exact Or.inr hyb
  · by_cases hyi : part y = i
    · by_cases hxb : part x = part b
      ·
        rw [lasso, joinWalk_of_eq part hadj hba hxb.symm,
          joinWalk_of_ne part hadj hba (fun e => hb (e.trans hyi))]
        simp only [Walk.reverse_cons, Walk.reverse_nil, Walk.nil_append, Walk.cons_append]
        exact homotopic_quadrangle_nil _ _ _ _
          (hreach hb (fun e => hb (hxb.symm.trans e)) ha hyi)
      ·
        refine homotopic_nil_of_part part hadj (z := b) _ fun v hv => ?_
        rcases hs v hv with e | e | e | e <;> rw [e]
        · exact Or.inl rfl
        · exact Or.inr hba.symm
        · exact Or.inr hxb
        · exact Or.inr fun e => hb (e.symm.trans hyi)
    ·
      refine homotopic_nil_of_part part hadj (z := a) _ fun v hv => ?_
      rcases hs v hv with e | e | e | e <;> rw [e]
      · exact Or.inr hba
      · exact Or.inl rfl
      · exact Or.inr fun e => hxi (e.trans ha)
      · exact Or.inr fun e => hyi (e.trans ha)

end Join

end CFSG.Combinatorics
