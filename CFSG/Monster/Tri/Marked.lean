module

public import CFSG.YGroups.MarkedWalks

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.YGroups CFSG.Monster.B.Recog

variable {V : Type*} {G : SimpleGraph V} {T : V → V → V → Prop}

theorem permClosure_rotate {a b c : V} (h : permClosure T a b c) : permClosure T b c a := by
  unfold permClosure at h ⊢
  tauto

theorem markedHomotopic_left_cancel {u v w : V} (p : G.Walk u v) {q q' : G.Walk v w}
    (h : MarkedHomotopic T (p.append q) (p.append q')) : MarkedHomotopic T q q' := by
  have h1 : MarkedHomotopic T ((p.reverse.append p).append q) ((p.reverse.append p).append q') := by
    rw [← Walk.append_assoc, ← Walk.append_assoc]
    exact h.append_left p.reverse
  have h2 : ∀ r : G.Walk v w, MarkedHomotopic T ((p.reverse.append p).append r) r := fun r => by
    simpa using (markedHomotopic_reverse_append T p).append_right r
  exact (h2 q).symm.trans (h1.trans (h2 q'))

theorem markedHomotopic_right_cancel {u v w : V} {p p' : G.Walk u v} (q : G.Walk v w)
    (h : MarkedHomotopic T (p.append q) (p'.append q)) : MarkedHomotopic T p p' := by
  have h1 : MarkedHomotopic T (p.append (q.append q.reverse)) (p'.append (q.append q.reverse)) := by
    rw [Walk.append_assoc, Walk.append_assoc]
    exact h.append_right q.reverse
  have h2 : ∀ r : G.Walk u v, MarkedHomotopic T (r.append (q.append q.reverse)) r := fun r => by
    simpa using (markedHomotopic_append_reverse T q).append_left r
  exact (h2 p).symm.trans (h1.trans (h2 p'))

theorem markedHomotopic_reverse_of_append_nil {u v : V} {p : G.Walk u v} {q : G.Walk v u}
    (h : MarkedHomotopic T (p.append q) .nil) : MarkedHomotopic T p q.reverse :=
  markedHomotopic_right_cancel q (h.trans (markedHomotopic_reverse_append T q).symm)

theorem markedHomotopic_rotate_nil {u v : V} {p : G.Walk u v} {q : G.Walk v u}
    (h : MarkedHomotopic T (p.append q) .nil) : MarkedHomotopic T (q.append p) .nil :=
  ((markedHomotopic_reverse_of_append_nil h).append_left q).trans
    (markedHomotopic_append_reverse T q)

theorem markedHomotopic_triangle_nil {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) (hT : permClosure T a b c) :
    MarkedHomotopic T (Walk.cons hab (Walk.cons hbc (Walk.cons hca Walk.nil)) : G.Walk a a)
      Walk.nil :=
  (markedHomotopic_triangle (.nil : G.Walk a a) .nil hab hbc hca hT).symm

theorem markedHomotopic_edge_split {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hac : G.Adj a c) (hT : permClosure T a b c) :
    MarkedHomotopic T (Walk.cons hac Walk.nil : G.Walk a c)
      (Walk.cons hab (Walk.cons hbc Walk.nil)) := by
  have h1 : MarkedHomotopic T (Walk.cons hab (Walk.cons hbc Walk.nil) : G.Walk a c)
      (Walk.cons hab (Walk.cons hbc (Walk.cons hac.symm (Walk.cons hac Walk.nil)))) := by
    simpa using markedHomotopic_backtrack T (Walk.cons hab (Walk.cons hbc Walk.nil) : G.Walk a c)
      (Walk.nil : G.Walk c c) hac.symm
  have h2 : MarkedHomotopic T
      (Walk.cons hab (Walk.cons hbc (Walk.cons hac.symm (Walk.cons hac Walk.nil))) : G.Walk a c)
      (Walk.cons hac Walk.nil) := by
    simpa using (markedHomotopic_triangle_nil hab hbc hac.symm hT).append_right
      (Walk.cons hac Walk.nil)
  exact (h1.trans h2).symm

@[expose] def muGraph (T : V → V → V → Prop) (G : SimpleGraph V) (a c : V) :
    SimpleGraph (G.commonNeighbors a c) where
  Adj s t := G.Adj s t ∧ permClosure T a s t ∧ permClosure T c s t
  symm := ⟨fun _ _ h => ⟨h.1.symm, permClosure_swap h.2.1, permClosure_swap h.2.2⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

theorem markedHomotopic_path_two_step {a c d d' : V} (had : G.Adj a d) (hdc : G.Adj d c)
    (had' : G.Adj a d') (hd'c : G.Adj d' c) (hdd' : G.Adj d d') (h₁ : permClosure T a d d')
    (h₂ : permClosure T c d d') :
    MarkedHomotopic T (Walk.cons had (Walk.cons hdc Walk.nil) : G.Walk a c)
      (Walk.cons had' (Walk.cons hd'c Walk.nil)) := by
  have e1 : MarkedHomotopic T (Walk.cons had Walk.nil : G.Walk a d)
      (Walk.cons had' (Walk.cons hdd'.symm Walk.nil)) :=
    markedHomotopic_edge_split had' hdd'.symm had (permClosure_swap h₁)
  have e2 : MarkedHomotopic T (Walk.cons hdc Walk.nil : G.Walk d c)
      (Walk.cons hdd' (Walk.cons hd'c Walk.nil)) :=
    markedHomotopic_edge_split hdd' hd'c hdc (permClosure_rotate h₂)
  have e3 : MarkedHomotopic T
      ((Walk.cons had (Walk.cons hdc Walk.nil) : G.Walk a c))
      ((Walk.cons had' (Walk.cons hdd'.symm Walk.nil)).append
        (Walk.cons hdd' (Walk.cons hd'c Walk.nil))) := by
    simpa using e1.append e2
  have e4 : MarkedHomotopic T
      ((Walk.cons had' (Walk.cons hdd'.symm Walk.nil)).append
        (Walk.cons hdd' (Walk.cons hd'c Walk.nil)) : G.Walk a c)
      (Walk.cons had' (Walk.cons hd'c Walk.nil)) := by
    have := markedHomotopic_backtrack T (Walk.cons had' Walk.nil : G.Walk a d')
      (Walk.cons hd'c Walk.nil : G.Walk d' c) hdd'.symm
    simpa using this.symm
  exact e3.trans e4

private theorem markedHomotopic_path_two_of_walk {a c : V} {y₁ y₂ : G.commonNeighbors a c}
    (w : (muGraph T G a c).Walk y₁ y₂) :
    MarkedHomotopic T (Walk.cons (G.mem_commonNeighbors.1 y₁.2).1
        (Walk.cons (G.mem_commonNeighbors.1 y₁.2).2.symm Walk.nil) : G.Walk a c)
      (Walk.cons (G.mem_commonNeighbors.1 y₂.2).1
        (Walk.cons (G.mem_commonNeighbors.1 y₂.2).2.symm Walk.nil)) := by
  induction w with
  | nil => exact MarkedHomotopic.refl _
  | @cons y₁ y₂ y₃ h _ ih =>
    exact (markedHomotopic_path_two_step (G.mem_commonNeighbors.1 y₁.2).1
      (G.mem_commonNeighbors.1 y₁.2).2.symm (G.mem_commonNeighbors.1 y₂.2).1
      (G.mem_commonNeighbors.1 y₂.2).2.symm h.1 h.2.1 h.2.2).trans ih

theorem markedHomotopic_path_two_of_reachable {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (had : G.Adj a d) (hdc : G.Adj d c)
    (hr : (muGraph T G a c).Reachable
      ⟨b, G.mem_commonNeighbors.2 ⟨hab, hbc.symm⟩⟩ ⟨d, G.mem_commonNeighbors.2 ⟨had, hdc.symm⟩⟩) :
    MarkedHomotopic T (Walk.cons hab (Walk.cons hbc Walk.nil) : G.Walk a c)
      (Walk.cons had (Walk.cons hdc Walk.nil)) := by
  obtain ⟨w⟩ := hr
  exact markedHomotopic_path_two_of_walk w

theorem markedHomotopic_quadrangle_nil {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a)
    (hr : (muGraph T G a c).Reachable
      ⟨b, G.mem_commonNeighbors.2 ⟨hab, hbc.symm⟩⟩ ⟨d, G.mem_commonNeighbors.2 ⟨hda.symm, hcd⟩⟩) :
    MarkedHomotopic T (Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil))) :
      G.Walk a a) Walk.nil := by
  have h := markedHomotopic_path_two_of_reachable hab hbc hda.symm hcd.symm hr
  have h' := h.append_right (Walk.cons hcd (Walk.cons hda Walk.nil))
  have h'' : MarkedHomotopic T
      ((Walk.cons hda.symm (Walk.cons hcd.symm Walk.nil) : G.Walk a c).append
        (Walk.cons hcd (Walk.cons hda Walk.nil))) Walk.nil := by
    simpa using markedHomotopic_append_reverse T
      (Walk.cons hda.symm (Walk.cons hcd.symm Walk.nil) : G.Walk a c)
  simpa using h'.trans h''

theorem markedHomotopic_nil_or_of_short (hG : Triangulable G)
    (Short : ∀ {a : V}, G.Walk a a → Prop)
    (htri : ∀ {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a),
      permClosure T a b c ∨ Short (Walk.cons hab (Walk.cons hbc (Walk.cons hca Walk.nil))))
    {x : V} (τ : G.Walk x x) (hτ : MarkedHomotopic T (τ.append τ) .nil)
    (hconj : ∀ {x' : V} (A : G.Walk x x') (σ : G.Walk x' x'), Short σ →
      MarkedHomotopic T (A.append (σ.append A.reverse)) τ)
    (p : G.Walk x x) : MarkedHomotopic T p .nil ∨ MarkedHomotopic T p τ := by
  have hinv : ∀ {p q : G.Walk x x}, MarkedHomotopic T p q →
      ((MarkedHomotopic T p .nil ∨ MarkedHomotopic T p τ) ↔
        (MarkedHomotopic T q .nil ∨ MarkedHomotopic T q τ)) := by
    intro p q h
    constructor
    · rintro (h1 | h1)
      · exact Or.inl (h.symm.trans h1)
      · exact Or.inr (h.symm.trans h1)
    · rintro (h1 | h1)
      · exact Or.inl (h.trans h1)
      · exact Or.inr (h.trans h1)
  have hmul : ∀ {p : G.Walk x x},
      ((MarkedHomotopic T p .nil ∨ MarkedHomotopic T p τ) ↔
        (MarkedHomotopic T (τ.append p) .nil ∨ MarkedHomotopic T (τ.append p) τ)) := by
    intro p
    constructor
    · rintro (h1 | h1)
      · refine Or.inr ?_
        simpa using h1.append_left τ
      · exact Or.inl ((h1.append_left τ).trans hτ)
    · rintro (h1 | h1)
      · refine Or.inr (markedHomotopic_left_cancel τ (h1.trans hτ.symm))
      · refine Or.inl (markedHomotopic_left_cancel τ ?_)
        simpa using h1
  have hstep : ∀ {p q : G.Walk x x}, ElemMove p q →
      ((MarkedHomotopic T p .nil ∨ MarkedHomotopic T p τ) ↔
        (MarkedHomotopic T q .nil ∨ MarkedHomotopic T q τ)) := by
    intro p q h
    cases h with
    | backtrack p₁ q₁ h => exact hinv (markedHomotopic_backtrack T p₁ q₁ h)
    | @triangle a b c p₁ q₁ hxy hyz hzx =>
      by_cases hm : permClosure T a b c
      · exact hinv (markedHomotopic_triangle p₁ q₁ hxy hyz hzx hm)
      · have hs := (htri hxy hyz hzx).resolve_left hm
        obtain ⟨σ, hσ⟩ : ∃ σ : G.Walk a a, σ = Walk.cons hxy (Walk.cons hyz (Walk.cons hzx
          Walk.nil)) := ⟨_, rfl⟩
        have hQ : p₁.append (Walk.cons hxy (Walk.cons hyz (Walk.cons hzx q₁))) =
            p₁.append (σ.append q₁) := by
          subst hσ
          rfl
        rw [hQ]
        have h1 := hconj p₁ σ (hσ ▸ hs)
        have h3 : MarkedHomotopic T (p₁.reverse.append (p₁.append q₁)) q₁ := by
          rw [Walk.append_assoc]
          simpa using (markedHomotopic_reverse_append T p₁).append_right q₁
        have h5 := (h3.append_left σ).append_left p₁
        have e : (p₁.append (σ.append p₁.reverse)).append (p₁.append q₁) =
            p₁.append (σ.append (p₁.reverse.append (p₁.append q₁))) := by
          simp only [Walk.append_assoc]
        have h2 : MarkedHomotopic T (p₁.append (σ.append q₁))
            ((p₁.append (σ.append p₁.reverse)).append (p₁.append q₁)) := by
          rw [e]
          exact h5.symm
        have h6 := h2.trans (h1.append_right (p₁.append q₁))
        exact hmul.trans (hinv h6).symm
  have key : ∀ {q r : G.Walk x x}, Homotopic q r →
      ((MarkedHomotopic T q .nil ∨ MarkedHomotopic T q τ) ↔
        (MarkedHomotopic T r .nil ∨ MarkedHomotopic T r τ)) := by
    intro q r h
    induction h with
    | rel a b hab => exact hstep hab
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (key (hG x p)).2 (Or.inl (MarkedHomotopic.refl _))

theorem permClosure_map {V' : Type*} {T' : V' → V' → V' → Prop} (φ : V → V')
    (hφ : ∀ x y z, T x y z → T' (φ x) (φ y) (φ z)) {a b c : V} (h : permClosure T a b c) :
    permClosure T' (φ a) (φ b) (φ c) := by
  unfold permClosure at h ⊢
  rcases h with h | h | h | h | h | h
  · exact Or.inl (hφ _ _ _ h)
  · exact Or.inr (Or.inl (hφ _ _ _ h))
  · exact Or.inr (Or.inr (Or.inl (hφ _ _ _ h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hφ _ _ _ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hφ _ _ _ h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hφ _ _ _ h)))))

theorem markedHomotopic_map {V' : Type*} {G' : SimpleGraph V'} {T' : V' → V' → V' → Prop}
    (φ : G →g G') (hφ : ∀ x y z, T x y z → T' (φ x) (φ y) (φ z)) {u v : V}
    {p q : G.Walk u v} (h : MarkedHomotopic T p q) :
    MarkedHomotopic T' (p.map φ) (q.map φ) := by
  induction h with
  | rel p q h =>
    cases h with
    | backtrack p q h =>
      have := markedHomotopic_backtrack T' (p.map φ) (q.map φ) (φ.map_adj h)
      simpa using this
    | triangle p q hxy hyz hzx hT =>
      have := markedHomotopic_triangle (T := T') (p.map φ) (q.map φ) (φ.map_adj hxy)
        (φ.map_adj hyz) (φ.map_adj hzx) (permClosure_map φ hφ hT)
      simpa using this
  | refl p => exact MarkedHomotopic.refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end CFSG.Monster.Tri
