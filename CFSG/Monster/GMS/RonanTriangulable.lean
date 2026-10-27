module

public import CFSG.Monster.B.Recog.GenericWalkHomotopy
public import Mathlib.Combinatorics.SimpleGraph.Metric

public section

namespace CFSG.Monster.GMS

open SimpleGraph CFSG.Monster.B.Recog

variable {V : Type*} {G : SimpleGraph V}

private theorem homotopic_cons_cons_symm {x y v : V} (h : G.Adj x y) (w : G.Walk x v) :
    Homotopic (.cons h (.cons h.symm w)) w := by
  simpa using (homotopic_backtrack (.nil : G.Walk x x) w h).symm

private theorem homotopic_cons_triangle {x y z v : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hxz : G.Adj x z) (w : G.Walk z v) :
    Homotopic (.cons hxz w) (.cons hxy (.cons hyz w)) := by
  have h₁ := homotopic_triangle (.nil : G.Walk x x) (.cons hxz w) hxy hyz hxz.symm
  have h₂ : Homotopic (.cons hxy (.cons hyz (.cons hxz.symm (.cons hxz w))))
      (.cons hxy (.cons hyz w)) :=
    ((homotopic_cons_cons_symm hxz.symm w).cons hyz).cons hxy
  rw [Walk.nil_append, Walk.nil_append] at h₁
  exact h₁.trans h₂

private def geodesicsHomotopic (G : SimpleGraph V) (i : ℕ) : Prop :=
  ∀ ⦃x y : V⦄ (p q : G.Walk x y), G.dist x y = i → p.length = i → q.length = i → Homotopic p q

private def edgeHomotopic (G : SimpleGraph V) (i : ℕ) : Prop :=
  ∀ ⦃x y b : V⦄ (h : G.Adj x y) (p : G.Walk x b) (q : G.Walk y b),
    G.dist x b = i → G.dist y b = i → p.length = i → q.length = i → Homotopic p (.cons h q)

private theorem dist_adj_cases {x y : V} (h : G.Adj x y) (b : V) :
    G.dist x b = G.dist y b ∨ G.dist x b = G.dist y b + 1 ∨ G.dist y b = G.dist x b + 1 := by
  have := h.diff_dist_adj (u := b)
  rw [dist_comm (u := b) (v := x), dist_comm (u := b) (v := y)] at this
  omega

private theorem length_eq_dist_of_cons {x c y : V} (h : G.Adj x c) (p : G.Walk c y)
    (hp : (Walk.cons h p).length = G.dist x y) : p.length = G.dist c y := by
  have h₁ := dist_le p
  have h₂ := dist_adj_cases h y
  rw [Walk.length_cons] at hp
  omega

private theorem length_append_edge {u v w : V} (δ : G.Walk u v) (h : G.Adj v w) :
    (δ.append (.cons h .nil)).length = δ.length + 1 :=
  Walk.length_append δ _

private theorem geodesicsHomotopic_of_le_one {m : ℕ} (hm : m ≤ 1) : geodesicsHomotopic G m := by
  intro x y p q _ hp hq
  obtain rfl := Walk.eq_of_length_le_one (p := p) (q := q) (by omega) (by omega)
  exact Homotopic.refl _

private theorem edgeHomotopic_zero : edgeHomotopic G 0 := by
  intro x y b h p q _ _ hp hq
  exact absurd ((Walk.eq_of_length_eq_zero hp).trans (Walk.eq_of_length_eq_zero hq).symm) h.ne

private theorem edgeHomotopic_one : edgeHomotopic G 1 := by
  intro x y b h p q _ _ hp hq
  have hxb := Walk.adj_of_length_eq_one hp
  have hyb := Walk.adj_of_length_eq_one hq
  obtain rfl : p = .cons hxb .nil := Walk.eq_of_length_le_one (by omega) le_rfl
  obtain rfl : q = .cons hyb .nil := Walk.eq_of_length_le_one (by omega) le_rfl
  exact homotopic_cons_triangle h hyb hxb .nil

private theorem homotopic_cons_of_dist_lt {i : ℕ} (hP : ∀ m ≤ i, geodesicsHomotopic G m)
    (hQ : ∀ m < i, edgeHomotopic G m) {x y b : V} (h : G.Adj x y) (hy : G.dist y b < i)
    (p : G.Walk x b) (q : G.Walk y b) (hp : p.length = G.dist x b) (hq : q.length = G.dist y b) :
    Homotopic p (.cons h q) := by
  rcases dist_adj_cases h b with hxy | hxy | hxy
  · exact hQ _ (by omega) h p q rfl hxy.symm hp (hq.trans hxy.symm)
  · exact hP _ (by omega) p (.cons h q) rfl hp (by rw [Walk.length_cons, hq]; omega)
  · have h₁ := hP _ (by omega) q (.cons h.symm p) rfl hq (by rw [Walk.length_cons, hp]; omega)
    exact ((h₁.cons h).trans (homotopic_cons_cons_symm h p)).symm

private theorem homotopic_geodesic_of_length_le {i : ℕ} (hP : ∀ m ≤ i, geodesicsHomotopic G m)
    (hQ : ∀ m < i, edgeHomotopic G m) {x b : V} (p : G.Walk x b) (hp : p.length ≤ i)
    (γ : G.Walk x b) (hγ : γ.length = G.dist x b) : Homotopic p γ := by
  induction p with
  | nil =>
    have h₀ : γ.length = 0 := by rw [hγ, dist_self]
    obtain rfl : γ = .nil := Walk.eq_of_length_le_one (by omega) zero_le_one
    exact Homotopic.refl _
  | @cons x x' b h p ih =>
    obtain ⟨γ', hγ'⟩ := p.reachable.exists_walk_length_eq_dist
    rw [Walk.length_cons] at hp
    have h₁ := ih (by omega) γ' hγ'
    have h₂ := homotopic_cons_of_dist_lt hP hQ h (by have := dist_le p; omega) γ γ' hγ hγ'
    exact (h₁.cons h).trans h₂.symm

private theorem homotopic_cons_of_induce_preconnected {m : ℕ} (hP : geodesicsHomotopic G m)
    (hQ : edgeHomotopic G m) {x y : V} (S : Set V) (hadj : ∀ z ∈ S, G.Adj x z)
    (hdist : ∀ z ∈ S, G.dist z y = m) (hpc : (G.induce S).Preconnected) {c c' : V}
    (hc : c ∈ S) (hc' : c' ∈ S) (p : G.Walk c y) (q : G.Walk c' y) (hp : p.length = m)
    (hq : q.length = m) : Homotopic (.cons (hadj c hc) p) (.cons (hadj c' hc') q) := by
  obtain ⟨r⟩ := hpc ⟨c, hc⟩ ⟨c', hc'⟩
  suffices ∀ (u u' : S) (_ : (G.induce S).Walk u u') (p : G.Walk u y) (q : G.Walk u' y),
      p.length = m → q.length = m →
        Homotopic (.cons (hadj u u.prop) p) (.cons (hadj u' u'.prop) q) from
    this ⟨c, hc⟩ ⟨c', hc'⟩ r p q hp hq
  intro u u' r
  induction r with
  | nil => exact fun p q hp hq => (hP p q (hdist _ (Subtype.prop _)) hp hq).cons _
  | @cons u v w huv r ih =>
    intro p q hp hq
    have huv' : G.Adj u v := huv
    obtain ⟨γ, hγ⟩ := (huv'.symm.reachable.trans p.reachable).exists_walk_length_eq_dist
    rw [hdist v v.prop] at hγ
    have h₁ : Homotopic p (.cons huv' γ) := hQ huv' p γ (hdist u u.prop) (hdist v v.prop) hp hγ
    have h₂ := (h₁.cons (hadj u u.prop)).trans
      (homotopic_cons_triangle (hadj u u.prop) huv' (hadj v v.prop) γ).symm
    exact h₂.trans (ih γ q hγ hq)

private theorem geodesicsHomotopic_step {i : ℕ} (hi : 2 ≤ i)
    (hnbrs : ∀ a b, G.dist a b = i →
      (G.induce {c | G.Adj a c ∧ G.dist c b = i - 1}).Preconnected)
    (hP : geodesicsHomotopic G (i - 1)) (hQ : edgeHomotopic G (i - 1)) :
    geodesicsHomotopic G i := by
  intro x y p q hd hp hq
  cases p with
  | nil => rw [Walk.length_nil] at hp; omega
  | @cons _ c _ hxc p₁ =>
    cases q with
    | nil => rw [Walk.length_nil] at hq; omega
    | @cons _ c' _ hxc' q₁ =>
      have hc := length_eq_dist_of_cons hxc p₁ (hp.trans hd.symm)
      have hc' := length_eq_dist_of_cons hxc' q₁ (hq.trans hd.symm)
      rw [Walk.length_cons] at hp hq
      exact homotopic_cons_of_induce_preconnected hP hQ
        {c | G.Adj x c ∧ G.dist c y = i - 1} (fun _ hz => hz.left) (fun _ hz => hz.right)
        (hnbrs x y hd) ⟨hxc, by omega⟩ ⟨hxc', by omega⟩ p₁ q₁ (by omega) (by omega)

private theorem edgeHomotopic_step {i : ℕ} (hi : 2 ≤ i)
    (htri : ∀ a b g, G.dist a b = i → G.dist a g = i → G.Adj b g →
      ∃ c c', G.Adj a c ∧ G.dist c b = i - 1 ∧ G.Adj a c' ∧ G.dist c' g = i - 1 ∧
        (c = c' ∨ G.Adj c c'))
    (hP : ∀ m ≤ i, geodesicsHomotopic G m) (hQ : ∀ m < i, edgeHomotopic G m) :
    edgeHomotopic G i := by
  intro x y b h p q hxb hyb hp hq
  obtain ⟨c, c', hbc, hcx, hbc', hc'y, hcc'⟩ :=
    htri b x y (by rwa [dist_comm]) (by rwa [dist_comm]) h
  rw [dist_comm] at hcx hc'y
  obtain ⟨δx, hδx⟩ := exists_walk_of_dist_ne_zero (G := G) (u := x) (v := c) (by omega)
  obtain ⟨δy, hδy⟩ := exists_walk_of_dist_ne_zero (G := G) (u := y) (v := c') (by omega)
  rw [hcx] at hδx
  rw [hc'y] at hδy
  have hp' : Homotopic p (δx.append (.cons hbc.symm .nil)) :=
    hP i le_rfl p _ hxb hp (by rw [length_append_edge, hδx]; omega)
  have hq' : Homotopic q (δy.append (.cons hbc'.symm .nil)) :=
    hP i le_rfl q _ hyb hq (by rw [length_append_edge, hδy]; omega)
  have key : ∀ Y : G.Walk y c, Homotopic (.cons h.symm δx) Y →
      Homotopic (Y.append (.cons hbc.symm .nil)) q → Homotopic p (.cons h q) := by
    intro Y hXY hYq
    have h₁ : Homotopic δx (.cons h Y) :=
      (homotopic_cons_cons_symm h δx).symm.trans (hXY.cons h)
    have h₂ := h₁.append_right (.cons hbc.symm .nil)
    rw [Walk.cons_append] at h₂
    exact hp'.trans (h₂.trans (hYq.cons h))
  obtain ⟨γ, hγ⟩ := (h.symm.reachable.trans δx.reachable).exists_walk_length_eq_dist
  have hW : ∀ Y : G.Walk y c, Y.length ≤ i → Homotopic Y γ := fun Y hY =>
    homotopic_geodesic_of_length_le hP hQ Y hY γ hγ
  have hX : Homotopic (.cons h.symm δx) γ := hW _ (by rw [Walk.length_cons, hδx]; omega)
  rcases hcc' with rfl | hcc'
  · exact key δy (hX.trans (hW δy (by omega)).symm) hq'.symm
  · refine key (δy.append (.cons hcc'.symm .nil)) (hX.trans (hW _ ?_).symm) ?_
    · rw [length_append_edge, hδy]; omega
    · rw [← Walk.append_assoc, Walk.cons_append, Walk.nil_append]
      exact ((homotopic_cons_triangle hcc'.symm hbc.symm hbc'.symm .nil).symm.append_left
        δy).trans hq'.symm

private theorem forall_geodesicsHomotopic_and_edgeHomotopic
    (hnbrs : ∀ i, 2 ≤ i → ∀ a b, G.dist a b = i →
      (G.induce {c | G.Adj a c ∧ G.dist c b = i - 1}).Preconnected)
    (htri : ∀ i, 2 ≤ i → ∀ a b g, G.dist a b = i → G.dist a g = i → G.Adj b g →
      ∃ c c', G.Adj a c ∧ G.dist c b = i - 1 ∧ G.Adj a c' ∧ G.dist c' g = i - 1 ∧
        (c = c' ∨ G.Adj c c')) :
    ∀ i, geodesicsHomotopic G i ∧ edgeHomotopic G i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · exact ⟨geodesicsHomotopic_of_le_one zero_le_one, edgeHomotopic_zero⟩
      · exact ⟨geodesicsHomotopic_of_le_one le_rfl, edgeHomotopic_one⟩
    · obtain ⟨hP₁, hQ₁⟩ := ih (i - 1) (by omega)
      have hP : geodesicsHomotopic G i := geodesicsHomotopic_step hi (hnbrs i hi) hP₁ hQ₁
      refine ⟨hP, edgeHomotopic_step hi (htri i hi) (fun m hm => ?_) fun m hm => (ih m hm).right⟩
      rcases hm.lt_or_eq with hm | rfl
      · exact (ih m hm).left
      · exact hP

theorem triangulable_of_ronan_of_all_levels
    (hnbrs : ∀ i, 2 ≤ i → ∀ a b, G.dist a b = i →
      (G.induce {c | G.Adj a c ∧ G.dist c b = i - 1}).Preconnected)
    (htri : ∀ i, 2 ≤ i → ∀ a b g, G.dist a b = i → G.dist a g = i → G.Adj b g →
      ∃ c c', G.Adj a c ∧ G.dist c b = i - 1 ∧ G.Adj a c' ∧ G.dist c' g = i - 1 ∧
        (c = c' ∨ G.Adj c c')) :
    Triangulable G := by
  have key := forall_geodesicsHomotopic_and_edgeHomotopic hnbrs htri
  intro u p
  exact homotopic_geodesic_of_length_le (i := p.length) (fun m _ => (key m).left)
    (fun m _ => (key m).right) p le_rfl .nil dist_self.symm

theorem triangulable_of_ronan {d : ℕ} (hd : ∀ x y, G.dist x y ≤ d)
    (hnbrs : ∀ i, 2 ≤ i → i ≤ d → ∀ a b, G.dist a b = i →
      (G.induce {c | G.Adj a c ∧ G.dist c b = i - 1}).Preconnected)
    (htri : ∀ i, 2 ≤ i → i ≤ d → ∀ a b g, G.dist a b = i → G.dist a g = i → G.Adj b g →
      ∃ c c', G.Adj a c ∧ G.dist c b = i - 1 ∧ G.Adj a c' ∧ G.dist c' g = i - 1 ∧
        (c = c' ∨ G.Adj c c')) :
    Triangulable G :=
  triangulable_of_ronan_of_all_levels
    (fun i hi a b hab => hnbrs i hi (by have := hd a b; omega) a b hab)
    (fun i hi a b g hab => htri i hi (by have := hd a b; omega) a b g hab)

end CFSG.Monster.GMS
