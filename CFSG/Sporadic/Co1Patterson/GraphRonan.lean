module

public import CFSG.Monster.B.Recog.GenericWalkHomotopy
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Sporadic.Co1Patterson

open SimpleGraph CFSG.Monster.B.Recog

variable {V : Type*} {G : SimpleGraph V}

private theorem cons_cons_symm {x y v : V} (h : G.Adj x y) (w : G.Walk x v) :
    Homotopic (.cons h (.cons h.symm w)) w := by
  simpa using (homotopic_backtrack (.nil : G.Walk x x) w h).symm

private theorem cons_triangle {x y z v : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hxz : G.Adj x z) (w : G.Walk z v) :
    Homotopic (.cons hxz w) (.cons hxy (.cons hyz w)) := by
  have h₁ := homotopic_triangle (.nil : G.Walk x x) (.cons hxz w) hxy hyz hxz.symm
  have h₂ : Homotopic (.cons hxy (.cons hyz (.cons hxz.symm (.cons hxz w))))
      (.cons hxy (.cons hyz w)) :=
    ((cons_cons_symm hxz.symm w).cons hyz).cons hxy
  rw [Walk.nil_append, Walk.nil_append] at h₁
  exact h₁.trans h₂

theorem homotopic_of_append_reverse {u v : V} {p q : G.Walk u v}
    (h : Homotopic (p.append q.reverse) .nil) : Homotopic p q := by
  have h₁ : Homotopic (p.append (q.reverse.append q)) p := by
    simpa using (homotopic_reverse_append q).append_left p
  have h₂ : Homotopic ((p.append q.reverse).append q) q := by
    simpa using h.append_right q
  rw [← Walk.append_assoc] at h₂
  exact h₁.symm.trans h₂

theorem homotopic_cons_nil_of_append {x y : V} (e : G.Adj x y) (q : G.Walk y x)
    (h : Homotopic (q.append (.cons e .nil)) .nil) : Homotopic (.cons e q) .nil := by
  have h₁ : Homotopic (Walk.cons e q) (.cons e (q.append (.cons e (.cons e.symm .nil)))) := by
    simpa using homotopic_backtrack (Walk.cons e q) .nil e
  have h₂ : Homotopic (Walk.cons e (q.append (.cons e (.cons e.symm .nil))))
      (.cons e (.cons e.symm .nil)) := by
    have := (h.append_right (Walk.cons e.symm .nil)).cons e
    rw [← Walk.append_assoc, Walk.cons_append, Walk.nil_append] at this
    simpa using this
  exact h₁.trans (h₂.trans (homotopic_cons_cons_nil e))

@[expose] def ShortNull (G : SimpleGraph V) : Prop :=
  ∀ (u : V) (p : G.Walk u u), p.length ≤ 4 → Homotopic p .nil

theorem dist_eq_two_of_walk {u w : V} (p : G.Walk u w) (hp : p.length = 2) (hne : u ≠ w)
    (hadj : ¬ G.Adj u w) : G.dist u w = 2 := by
  have h₁ := dist_le p
  have h₀ : G.dist u w ≠ 0 := fun h => hne ((p.reachable.dist_eq_zero_iff).1 h)
  have h₂ : G.dist u w ≠ 1 := fun h => hadj (dist_eq_one_iff_adj.1 h)
  omega

theorem shortNull_of_geodesics
    (hP : ∀ ⦃x y : V⦄ (p q : G.Walk x y), G.dist x y = 2 → p.length = 2 → q.length = 2 →
      Homotopic p q) : ShortNull G := by
  intro u p hp
  cases p with
  | nil => exact Homotopic.refl _
  | cons h₁ p =>
    cases p with
    | nil => exact (G.irrefl h₁).elim
    | cons h₂ p =>
      cases p with
      | nil => exact homotopic_cons_cons_nil h₁
      | cons h₃ p =>
        cases p with
        | nil => exact (homotopic_triangle .nil .nil h₁ h₂ h₃).symm
        | cons h₄ p =>
          cases p with
          | cons h₅ p => simp at hp; omega
          | nil =>
            rename_i v w x
            by_cases hw : u = w
            · subst hw
              exact (cons_cons_symm h₁ _).trans (homotopic_cons_cons_nil h₃)
            by_cases hc : G.Adj u w
            · have e₁ : Homotopic (Walk.cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))))
                  (.cons hc (.cons h₃ (.cons h₄ .nil))) :=
                (cons_triangle h₁ h₂ hc _).symm
              exact e₁.trans (homotopic_triangle .nil .nil hc h₃ h₄).symm
            · have hd := dist_eq_two_of_walk (Walk.cons h₁ (.cons h₂ .nil)) rfl hw hc
              have e₁ : Homotopic (Walk.cons h₁ (.cons h₂ .nil))
                  (.cons h₄.symm (.cons h₃.symm .nil)) := hP _ _ hd rfl rfl
              have e₂ := e₁.append_right (Walk.cons h₃ (.cons h₄ .nil))
              have e₃ : Homotopic (Walk.cons h₄.symm (.cons h₃.symm (.cons h₃ (.cons h₄ .nil))))
                  .nil :=
                ((cons_cons_symm h₃.symm _).cons h₄.symm).trans (homotopic_cons_cons_nil h₄.symm)
              exact e₂.trans e₃

@[expose] def pentWalk {v₀ v₁ v₂ v₃ v₄ : V} (h₀₁ : G.Adj v₀ v₁) (h₁₂ : G.Adj v₁ v₂)
    (h₂₃ : G.Adj v₂ v₃) (h₃₄ : G.Adj v₃ v₄) (h₄₀ : G.Adj v₄ v₀) : G.Walk v₀ v₀ :=
  .cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil))))

inductive PentNull (G : SimpleGraph V) : V → V → V → V → V → Prop
  | chord {v₀ v₁ v₂ v₃ v₄ : V} (h : v₀ = v₂ ∨ G.Adj v₀ v₂) : PentNull G v₀ v₁ v₂ v₃ v₄
  | centre {v₀ v₁ v₂ v₃ v₄ z : V} (h₀ : G.Adj z v₀) (h₂ : G.Adj z v₂) (h₃ : G.Adj z v₃) :
      PentNull G v₀ v₁ v₂ v₃ v₄
  | split {v₀ v₁ v₂ v₃ v₄ z : V} (h₀ : G.Adj z v₀) (h₂ : G.Adj z v₂)
      (h : PentNull G v₀ z v₂ v₃ v₄) : PentNull G v₀ v₁ v₂ v₃ v₄
  | rot {v₀ v₁ v₂ v₃ v₄ : V} (h : PentNull G v₁ v₂ v₃ v₄ v₀) : PentNull G v₀ v₁ v₂ v₃ v₄

private theorem homotopic_of_short (hS : ShortNull G) {u v : V} {p q : G.Walk u v}
    (h : p.length + q.length ≤ 4) : Homotopic p q :=
  homotopic_of_append_reverse (hS u _ (by simpa [Walk.length_append] using h))

theorem PentNull.homotopic (hS : ShortNull G) {v₀ v₁ v₂ v₃ v₄ : V}
    (hP : PentNull G v₀ v₁ v₂ v₃ v₄) :
    ∀ (h₀₁ : G.Adj v₀ v₁) (h₁₂ : G.Adj v₁ v₂) (h₂₃ : G.Adj v₂ v₃) (h₃₄ : G.Adj v₃ v₄)
      (h₄₀ : G.Adj v₄ v₀), Homotopic (pentWalk h₀₁ h₁₂ h₂₃ h₃₄ h₄₀) .nil := by
  induction hP with
  | @chord v₀ v₁ v₂ v₃ v₄ h =>
    intro h₀₁ h₁₂ h₂₃ h₃₄ h₄₀
    rcases h with rfl | hc
    · exact (cons_cons_symm h₀₁ _).trans (hS _ _ (by simp))
    · have e : Homotopic (Walk.cons h₀₁ (.cons h₁₂ .nil)) (.cons hc .nil) :=
        homotopic_of_short hS (by simp)
      exact (e.append_right (Walk.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil)))).trans
        (hS _ _ (by simp))
  | @centre v₀ v₁ v₂ v₃ v₄ z hz₀ hz₂ hz₃ =>
    intro h₀₁ h₁₂ h₂₃ h₃₄ h₄₀
    have e₁ : Homotopic (Walk.cons h₀₁ (.cons h₁₂ .nil)) (.cons hz₀.symm (.cons hz₂ .nil)) :=
      homotopic_of_short hS (by simp)
    have e₂ : Homotopic (Walk.cons h₂₃ .nil) (.cons hz₂.symm (.cons hz₃ .nil)) :=
      homotopic_of_short hS (by simp)
    have e₃ : Homotopic (Walk.cons h₃₄ (.cons h₄₀ .nil)) (.cons hz₃.symm (.cons hz₀ .nil)) :=
      homotopic_of_short hS (by simp)
    have e := e₁.append (e₂.append e₃)
    refine e.trans ?_
    simp only [Walk.cons_append, Walk.nil_append]
    exact (((cons_cons_symm hz₂ _).trans (cons_cons_symm hz₃ _)).cons hz₀.symm).trans
      (homotopic_cons_cons_nil hz₀.symm)
  | @split v₀ v₁ v₂ v₃ v₄ z hz₀ hz₂ _ ih =>
    intro h₀₁ h₁₂ h₂₃ h₃₄ h₄₀
    have e : Homotopic (Walk.cons h₀₁ (.cons h₁₂ .nil)) (.cons hz₀.symm (.cons hz₂ .nil)) :=
      homotopic_of_short hS (by simp)
    exact (e.append_right (Walk.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil)))).trans
      (ih hz₀.symm hz₂ h₂₃ h₃₄ h₄₀)
  | @rot v₀ v₁ v₂ v₃ v₄ _ ih =>
    intro h₀₁ h₁₂ h₂₃ h₃₄ h₄₀
    exact homotopic_cons_nil_of_append h₀₁ _ (ih h₁₂ h₂₃ h₃₄ h₄₀ h₀₁)

theorem PentNull.rot₂ {v₀ v₁ v₂ v₃ v₄ : V} (h : PentNull G v₀ v₁ v₂ v₃ v₄) :
    PentNull G v₂ v₃ v₄ v₀ v₁ :=
  .rot (.rot (.rot h))

inductive Q2Good (G : SimpleGraph V) (a : V) : V → V → Prop
  | pent {b g c c' : V} (hac : G.Adj a c) (hcb : G.Adj c b) (hbg : G.Adj b g)
      (hgc' : G.Adj g c') (hc'a : G.Adj c' a) (h : PentNull G a c b g c') : Q2Good G a b g
  | prop {b x g : V} (hbg : G.Adj b g) (h₁ : Q2Good G a b x) (h₂ : Q2Good G a x g) :
      Q2Good G a b g

theorem Q2Good.q2At (hS : ShortNull G) {a b g : V} (h : Q2Good G a b g) :
    ∃ (h : G.Adj b g) (p : G.Walk b a) (q : G.Walk g a), p.length = 2 ∧ q.length = 2 ∧
      Homotopic p (.cons h q) := by
  induction h with
  | @pent b g c c' hac hcb hbg hgc' hc'a hP =>
    refine ⟨hbg, .cons hcb.symm (.cons hac.symm .nil), .cons hgc' (.cons hc'a .nil), rfl, rfl,
      ?_⟩
    have e := hP.rot₂.homotopic hS hbg hgc' hc'a hac hcb
    have e' : Homotopic ((Walk.cons hbg (.cons hgc' (.cons hc'a .nil))).append
        (Walk.cons hcb.symm (.cons hac.symm .nil)).reverse) .nil := by
      simpa [pentWalk] using e
    exact (homotopic_of_append_reverse e').symm
  | @prop b x g hbg _ _ ih₁ ih₂ =>
    obtain ⟨hbx, p₁, q₁, hp₁, hq₁, e₁⟩ := ih₁
    obtain ⟨hxg, p₂, q₂, hp₂, hq₂, e₂⟩ := ih₂
    have e₃ : Homotopic q₁ p₂ := homotopic_of_short hS (by omega)
    refine ⟨hbg, p₁, q₂, hp₁, hq₂, ?_⟩
    exact e₁.trans (((e₃.trans e₂).cons hbx).trans (cons_triangle hbx hxg hbg q₂).symm)

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
  exact cons_triangle h hyb hxb .nil

private theorem homotopic_cons_of_dist_lt {i : ℕ} (hP : ∀ m ≤ i, geodesicsHomotopic G m)
    (hQ : ∀ m < i, edgeHomotopic G m) {x y b : V} (h : G.Adj x y) (hy : G.dist y b < i)
    (p : G.Walk x b) (q : G.Walk y b) (hp : p.length = G.dist x b) (hq : q.length = G.dist y b) :
    Homotopic p (.cons h q) := by
  rcases dist_adj_cases h b with hxy | hxy | hxy
  · exact hQ _ (by omega) h p q rfl hxy.symm hp (hq.trans hxy.symm)
  · exact hP _ (by omega) p (.cons h q) rfl hp (by rw [Walk.length_cons, hq]; omega)
  · have h₁ := hP _ (by omega) q (.cons h.symm p) rfl hq (by rw [Walk.length_cons, hp]; omega)
    exact ((h₁.cons h).trans (cons_cons_symm h p)).symm

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
      (cons_triangle (hadj u u.prop) huv' (hadj v v.prop) γ).symm
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
      (cons_cons_symm h δx).symm.trans (hXY.cons h)
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
      exact ((cons_triangle hcc'.symm hbc.symm hbc'.symm .nil).symm.append_left
        δy).trans hq'.symm

private theorem edgeHomotopic_two (hP : geodesicsHomotopic G 2)
    (hq2 : ∀ a b g, G.dist a b = 2 → G.dist a g = 2 → G.Adj b g → Q2Good G a b g) :
    edgeHomotopic G 2 := by
  intro x y b h p q hxb hyb hp hq
  have hS : ShortNull G := shortNull_of_geodesics hP
  obtain ⟨_h, p', q', hp', hq', he⟩ :=
    (hq2 b x y (by rwa [dist_comm]) (by rwa [dist_comm]) h).q2At hS
  exact (hP p p' hxb hp hp').trans (he.trans ((hP q' q hyb hq' hq).cons h))

private theorem forall_geodesics_and_edge
    (hnbrs : ∀ i, 2 ≤ i → ∀ a b, G.dist a b = i →
      (G.induce {c | G.Adj a c ∧ G.dist c b = i - 1}).Preconnected)
    (hq2 : ∀ a b g, G.dist a b = 2 → G.dist a g = 2 → G.Adj b g → Q2Good G a b g)
    (htri : ∀ i, 3 ≤ i → ∀ a b g, G.dist a b = i → G.dist a g = i → G.Adj b g →
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
      refine ⟨hP, ?_⟩
      rcases hi.lt_or_eq with hi3 | rfl
      · refine edgeHomotopic_step hi (htri i hi3) (fun m hm => ?_) fun m hm => (ih m hm).right
        rcases hm.lt_or_eq with hm | rfl
        · exact (ih m hm).left
        · exact hP
      · exact edgeHomotopic_two hP hq2

theorem triangulable_of_ronan_q2 {d : ℕ} (hd : ∀ x y, G.dist x y ≤ d)
    (hnbrs : ∀ i, 2 ≤ i → i ≤ d → ∀ a b, G.dist a b = i →
      (G.induce {c | G.Adj a c ∧ G.dist c b = i - 1}).Preconnected)
    (hq2 : ∀ a b g, G.dist a b = 2 → G.dist a g = 2 → G.Adj b g → Q2Good G a b g)
    (htri : ∀ i, 3 ≤ i → i ≤ d → ∀ a b g, G.dist a b = i → G.dist a g = i → G.Adj b g →
      ∃ c c', G.Adj a c ∧ G.dist c b = i - 1 ∧ G.Adj a c' ∧ G.dist c' g = i - 1 ∧
        (c = c' ∨ G.Adj c c')) :
    Triangulable G := by
  have key := forall_geodesics_and_edge
    (fun i hi a b hab => hnbrs i hi (by have := hd a b; omega) a b hab) hq2
    (fun i hi a b g hab => htri i hi (by have := hd a b; omega) a b g hab)
  intro u p
  exact homotopic_geodesic_of_length_le (i := p.length) (fun m _ => (key m).left)
    (fun m _ => (key m).right) p le_rfl .nil dist_self.symm

end CFSG.Sporadic.Co1Patterson
