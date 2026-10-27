module

public import CFSG.Monster.Tri.Marked

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.YGroups CFSG.Monster.B.Recog

variable {V : Type*} {G : SimpleGraph V} {mid : V → V → V} {lg : V → V → V → Prop}

structure ShortStruct (G : SimpleGraph V) (mid : V → V → V) (lg : V → V → V → Prop) : Prop where
  adj_mid_left : ∀ {x y : V}, G.Adj x y → G.Adj x (mid x y)
  adj_mid_right : ∀ {x y : V}, G.Adj x y → G.Adj y (mid x y)
  mid_mid : ∀ {x y : V}, G.Adj x y → mid x (mid x y) = y
  mid_comm : ∀ {x y : V}, G.Adj x y → mid y x = mid x y
  adj_mid_mid : ∀ {x y u : V}, G.Adj x y → G.Adj x u → G.Adj y u → permClosure lg x y u →
    G.Adj (mid x y) (mid x u)
  lg_iff : ∀ {x y z : V}, G.Adj x y → G.Adj y z → G.Adj z x →
    (permClosure lg x y z ↔ z ≠ mid x y)

@[expose] def ShortStruct.loop (S : ShortStruct G mid lg) {x y : V} (h : G.Adj x y) : G.Walk x x :=
  Walk.cons h (Walk.cons (S.adj_mid_right h) (Walk.cons (S.adj_mid_left h).symm Walk.nil))

@[expose] def ShortStruct.quad (S : ShortStruct G mid lg) {x y u : V} (hxy : G.Adj x y)
    (hxu : G.Adj x u) (hyu : G.Adj y u) (hL : permClosure lg x y u) : G.Walk y y :=
  Walk.cons hyu (Walk.cons (S.adj_mid_right hxu)
    (Walk.cons (S.adj_mid_mid hxy hxu hyu hL).symm (Walk.cons (S.adj_mid_right hxy).symm
      Walk.nil)))

@[expose] def longLinkGraph (G : SimpleGraph V) (lg : V → V → V → Prop) (x : V) :
    SimpleGraph (G.neighborSet x) where
  Adj s t := G.Adj s t ∧ permClosure lg x s t
  symm := ⟨fun _ _ h => ⟨h.1.symm, permClosure_swap h.2⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

theorem walk3_congr {a b c c' : V} (h : c = c') (h1 : G.Adj a b) (h2 : G.Adj b c)
    (h3 : G.Adj c a) (h2' : G.Adj b c') (h3' : G.Adj c' a) :
    (Walk.cons h1 (Walk.cons h2 (Walk.cons h3 Walk.nil)) : G.Walk a a) =
      Walk.cons h1 (Walk.cons h2' (Walk.cons h3' Walk.nil)) := by
  subst h
  rfl

theorem ShortStruct.loop_homotopic_of_long (S : ShortStruct G mid lg) {x y u : V}
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u) (hL : permClosure lg x y u)
    (hq : MarkedHomotopic lg (S.quad hxy hxu hyu hL) .nil) :
    MarkedHomotopic lg (S.loop hxy) (S.loop hxu) := by
  have hxz : G.Adj x (mid x y) := S.adj_mid_left hxy
  have hyz : G.Adj y (mid x y) := S.adj_mid_right hxy
  have hxv : G.Adj x (mid x u) := S.adj_mid_left hxu
  have huv : G.Adj u (mid x u) := S.adj_mid_right hxu
  have hzv : G.Adj (mid x y) (mid x u) := S.adj_mid_mid hxy hxu hyu hL
  have hL2 : permClosure lg x (mid x y) (mid x u) := by
    refine (S.lg_iff hxz hzv hxv.symm).2 ?_
    rw [S.mid_mid hxy]
    intro h
    have h1 : mid x y = u := by
      have := S.mid_mid hxu
      rwa [h] at this
    exact ((S.lg_iff hxy hyu hxu.symm).1 hL) h1.symm
  have hL1 : permClosure lg x u y := permClosure_swap hL
  have hL2' : permClosure lg (mid x y) (mid x u) x := permClosure_rotate hL2
  have e1 : MarkedHomotopic lg (Walk.cons hxy Walk.nil : G.Walk x y)
      (Walk.cons hxu (Walk.cons hyu.symm Walk.nil)) :=
    markedHomotopic_edge_split hxu hyu.symm hxy hL1
  have e2 : MarkedHomotopic lg (Walk.cons hxz.symm Walk.nil : G.Walk (mid x y) x)
      (Walk.cons hzv (Walk.cons hxv.symm Walk.nil)) :=
    markedHomotopic_edge_split hzv hxv.symm hxz.symm hL2'
  have hq1 : MarkedHomotopic lg (Walk.cons huv (Walk.cons hzv.symm
      (Walk.cons hyz.symm (Walk.cons hyu Walk.nil))) : G.Walk u u) Walk.nil := by
    have := markedHomotopic_rotate_nil (p := (Walk.cons hyu Walk.nil : G.Walk y u))
      (q := (Walk.cons huv (Walk.cons hzv.symm (Walk.cons hyz.symm Walk.nil)) :
        G.Walk u y)) hq
    simpa using this
  have eQ : MarkedHomotopic lg (Walk.cons huv Walk.nil : G.Walk u (mid x u))
      (Walk.cons hyu.symm (Walk.cons hyz (Walk.cons hzv Walk.nil))) := by
    have := markedHomotopic_reverse_of_append_nil
      (p := (Walk.cons huv Walk.nil : G.Walk u (mid x u)))
      (q := (Walk.cons hzv.symm (Walk.cons hyz.symm (Walk.cons hyu Walk.nil)) :
        G.Walk (mid x u) u)) (by simpa using hq1)
    simpa using this
  have c1 : MarkedHomotopic lg (S.loop hxy) (Walk.cons hxu (Walk.cons hyu.symm
      (Walk.cons hyz (Walk.cons hxz.symm Walk.nil)))) := by
    have := e1.append_right (Walk.cons hyz (Walk.cons hxz.symm Walk.nil))
    simpa [ShortStruct.loop] using this
  have c2 : MarkedHomotopic lg (Walk.cons hxu (Walk.cons hyu.symm
      (Walk.cons hyz (Walk.cons hxz.symm Walk.nil)))) (Walk.cons hxu (Walk.cons hyu.symm
      (Walk.cons hyz (Walk.cons hzv (Walk.cons hxv.symm Walk.nil))))) := by
    have := e2.append_left (Walk.cons hxu (Walk.cons hyu.symm (Walk.cons hyz Walk.nil)))
    simpa using this
  have c3 : MarkedHomotopic lg (Walk.cons hxu (Walk.cons hyu.symm
      (Walk.cons hyz (Walk.cons hzv (Walk.cons hxv.symm Walk.nil))))) (S.loop hxu) := by
    have := (eQ.symm.append_right (Walk.cons hxv.symm Walk.nil)).cons hxu
    simpa [ShortStruct.loop] using this
  exact c1.trans (c2.trans c3)

theorem ShortStruct.quad_null_of_mu (S : ShortStruct G mid lg) {x y u : V} (hxy : G.Adj x y)
    (hxu : G.Adj x u) (hyu : G.Adj y u) (hL : permClosure lg x y u)
    (hr : (muGraph lg G y (mid x u)).Reachable
      ⟨u, G.mem_commonNeighbors.2 ⟨hyu, (S.adj_mid_right hxu).symm⟩⟩
      ⟨mid x y, G.mem_commonNeighbors.2
        ⟨S.adj_mid_right hxy, (S.adj_mid_mid hxy hxu hyu hL).symm⟩⟩) :
    MarkedHomotopic lg (S.quad hxy hxu hyu hL) .nil :=
  markedHomotopic_quadrangle_nil hyu (S.adj_mid_right hxu) (S.adj_mid_mid hxy hxu hyu hL).symm
    (S.adj_mid_right hxy).symm hr

theorem ShortStruct.quad_null_of_mu_preconnected (S : ShortStruct G mid lg) {x y u : V}
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u) (hL : permClosure lg x y u)
    (hμ : (muGraph lg G y (mid x u)).Preconnected) :
    MarkedHomotopic lg (S.quad hxy hxu hyu hL) .nil :=
  S.quad_null_of_mu hxy hxu hyu hL (hμ _ _)

section Local

variable (S : ShortStruct G mid lg)
  (hq : ∀ {x y u : V} (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hL : permClosure lg x y u), MarkedHomotopic lg (S.quad hxy hxu hyu hL) .nil)

include hq in
theorem ShortStruct.loop_homotopic_of_reflTransGen {x : V} {s t : G.neighborSet x}
    (h : Relation.ReflTransGen (longLinkGraph G lg x).Adj s t) :
    MarkedHomotopic lg (S.loop (s.2 : G.Adj x s)) (S.loop (t.2 : G.Adj x t)) := by
  induction h with
  | refl => exact MarkedHomotopic.refl _
  | tail _ hbc ih =>
    exact ih.trans (S.loop_homotopic_of_long _ _ hbc.1 hbc.2 (hq _ _ hbc.1 hbc.2))

include hq in
theorem ShortStruct.loop_homotopic_of_reachable {x w w' : V} (hw : G.Adj x w)
    (hw' : G.Adj x w') (h : (longLinkGraph G lg x).Reachable ⟨w, hw⟩ ⟨w', hw'⟩) :
    MarkedHomotopic lg (S.loop hw) (S.loop hw') :=
  S.loop_homotopic_of_reflTransGen hq (SimpleGraph.reachable_iff_reflTransGen _ _ |>.1 h)

variable (hΩ : ∀ x, (longLinkGraph G lg x).Preconnected)

include hq hΩ in
theorem ShortStruct.loop_homotopic {x w w' : V} (hw : G.Adj x w) (hw' : G.Adj x w') :
    MarkedHomotopic lg (S.loop hw) (S.loop hw') :=
  S.loop_homotopic_of_reachable hq hw hw' (hΩ x _ _)

include hq hΩ in
theorem ShortStruct.loop_reverse_homotopic {x y : V} (hxy : G.Adj x y) :
    MarkedHomotopic lg (S.loop hxy).reverse (S.loop hxy) := by
  have hxz : G.Adj x (mid x y) := S.adj_mid_left hxy
  have h1 : (S.loop hxy).reverse = S.loop hxz := by
    have h2 : (S.loop hxy).reverse = (Walk.cons hxz (Walk.cons (S.adj_mid_right hxy).symm
        (Walk.cons hxy.symm Walk.nil)) : G.Walk x x) := by
      simp [ShortStruct.loop]
    rw [h2]
    exact walk3_congr (S.mid_mid hxy).symm _ _ _ _ _
  rw [h1]
  exact S.loop_homotopic hq hΩ hxz hxy

include hq hΩ in
theorem ShortStruct.loop_sq {x y : V} (hxy : G.Adj x y) :
    MarkedHomotopic lg ((S.loop hxy).append (S.loop hxy)) .nil :=
  (((S.loop_reverse_homotopic hq hΩ hxy).symm.append_left (S.loop hxy)).trans
    (markedHomotopic_append_reverse lg _))

include hq hΩ in
theorem ShortStruct.conj_loop_homotopic {x x' : V} (A : G.Walk x x') {y₀ w' : V}
    (hy₀ : G.Adj x y₀) (hw' : G.Adj x' w') :
    MarkedHomotopic lg (A.append ((S.loop hw').append A.reverse)) (S.loop hy₀) := by
  induction A generalizing y₀ with
  | nil => simpa using S.loop_homotopic hq hΩ hw' hy₀
  | @cons x x₁ x' e A' ih =>
    have ih' := ih e.symm hw'
    have h1 : MarkedHomotopic lg
        (((Walk.cons e A').append ((S.loop hw').append (Walk.cons e A').reverse)))
        (Walk.cons e ((S.loop e.symm).append (Walk.cons e.symm Walk.nil))) := by
      have h2 := (ih'.append_right (Walk.cons e.symm Walk.nil)).cons e
      simpa [Walk.append_assoc] using h2
    have hxm : G.Adj x (mid x₁ x) := S.adj_mid_right e.symm
    have h3 : MarkedHomotopic lg
        (Walk.cons e ((S.loop e.symm).append (Walk.cons e.symm Walk.nil)) : G.Walk x x)
        (Walk.cons hxm (Walk.cons (S.adj_mid_left e.symm).symm (Walk.cons e.symm Walk.nil))) := by
      have := (markedHomotopic_backtrack lg (.nil : G.Walk x x)
        (Walk.cons hxm (Walk.cons (S.adj_mid_left e.symm).symm (Walk.cons e.symm Walk.nil)) :
          G.Walk x x) e).symm
      simpa [ShortStruct.loop] using this
    have hc : x₁ = mid x (mid x₁ x) := by
      rw [S.mid_comm e, S.mid_mid e]
    have h4 : (Walk.cons hxm (Walk.cons (S.adj_mid_left e.symm).symm
        (Walk.cons e.symm Walk.nil)) : G.Walk x x) = S.loop hxm :=
      walk3_congr hc _ _ _ _ _
    rw [h4] at h3
    exact h1.trans (h3.trans (S.loop_homotopic hq hΩ hxm hy₀))

end Local

theorem homotopy_class_le_two (S : ShortStruct G mid lg) (hG : Triangulable G)
    (hΩ : ∀ x, (longLinkGraph G lg x).Preconnected)
    (hq : ∀ {x y u : V} (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
      (hL : permClosure lg x y u), MarkedHomotopic lg (S.quad hxy hxu hyu hL) .nil)
    {x y₀ : V} (hy₀ : G.Adj x y₀) (p : G.Walk x x) :
    MarkedHomotopic lg p .nil ∨ MarkedHomotopic lg p (S.loop hy₀) := by
  refine markedHomotopic_nil_or_of_short hG
    (fun {a} σ => ∃ (y : V) (h : G.Adj a y), σ = S.loop h) ?_ (S.loop hy₀)
    (S.loop_sq hq hΩ hy₀) ?_ p
  · intro a b c hab hbc hca
    by_cases hL : permClosure lg a b c
    · exact Or.inl hL
    · refine Or.inr ?_
      have hc : c = mid a b := by
        by_contra hne
        exact hL ((S.lg_iff hab hbc hca).2 hne)
      subst hc
      exact ⟨b, hab, rfl⟩
  · rintro x' A σ ⟨w', hw', rfl⟩
    exact S.conj_loop_homotopic hq hΩ A hy₀ hw'

section Fibres

variable {W : Type*} {H : SimpleGraph W} {f : H →g G}

theorem card_fibre_le_two (hf : IsCovering f) (ht : LiftsMarked f lg) (hH : H.Preconnected)
    {x : V} (τ : G.Walk x x)
    (hτ : ∀ p : G.Walk x x, MarkedHomotopic lg p .nil ∨ MarkedHomotopic lg p τ)
    {a b : W} (ha : f a = x) (hb : f b = x) :
    b = a ∨ b = hf.liftEnd τ a ha := by
  obtain ⟨q⟩ := hH a b
  have hend : hf.liftEnd ((q.map f).copy ha hb) a ha = b := by
    rw [hf.liftEnd_copy, hf.liftEnd_map]
  rcases hτ ((q.map f).copy ha hb) with h | h
  · left
    rw [← hend, h.liftEnd_eq hf ht a ha, liftEnd_nil_eq]
  · right
    rw [← hend, h.liftEnd_eq hf ht a ha]

theorem ncard_fibre_le_two (hf : IsCovering f) (ht : LiftsMarked f lg) (hH : H.Preconnected)
    {x : V} (τ : G.Walk x x)
    (hτ : ∀ p : G.Walk x x, MarkedHomotopic lg p .nil ∨ MarkedHomotopic lg p τ) :
    (f ⁻¹' {x}).ncard ≤ 2 := by
  by_cases hne : (f ⁻¹' {x}).Nonempty
  · obtain ⟨a, ha⟩ := hne
    have hsub : f ⁻¹' {x} ⊆ {a, hf.liftEnd τ a ha} := fun b hb => by
      rcases card_fibre_le_two hf ht hH τ hτ ha hb with h | h
      · exact Or.inl h
      · exact Or.inr h
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    simp
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    simp

end Fibres

end CFSG.Monster.Tri
