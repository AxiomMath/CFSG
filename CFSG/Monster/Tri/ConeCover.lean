module

public import CFSG.Monster.Tri.ClosedGen
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.B.Recog CFSG.Monster.B.GSide CFSG.YGroups

variable {V : Type*} {G : SimpleGraph V}

@[expose] def InducedNull (G : SimpleGraph V) (Φ : Set V) : Prop :=
  ∀ (u : V) (p : G.Walk u u), (∀ x ∈ p.support, x ∈ Φ) → Homotopic p .nil

@[expose] def DiamTwo (G : SimpleGraph V) (Φ : Set V) : Prop :=
  ∀ x ∈ Φ, ∀ y ∈ Φ, x = y ∨ G.Adj x y ∨ ∃ w ∈ Φ, G.Adj x w ∧ G.Adj w y

theorem DiamTwo.exists_walk {Φ : Set V} (h : DiamTwo G Φ) {x y : V} (hx : x ∈ Φ) (hy : y ∈ Φ) :
    ∃ q : G.Walk x y, q.length ≤ 2 ∧ ∀ w ∈ q.support, w ∈ Φ := by
  rcases h x hx y hy with rfl | hxy | ⟨w, hw, hxw, hwy⟩
  · exact ⟨.nil, by simp, by simpa using hx⟩
  · exact ⟨.cons hxy .nil, by simp, by simp [hx, hy]⟩
  · exact ⟨.cons hxw (.cons hwy .nil), by simp, by simp [hx, hw, hy]⟩

theorem exists_spoke {z x : V} (h : z = x ∨ G.Adj z x) : ∃ s : G.Walk z x, s.length ≤ 1 := by
  rcases h with rfl | h
  · exact ⟨.nil, by simp⟩
  · exact ⟨.cons h .nil, by simp⟩

structure ShortCongr (G : SimpleGraph V) (L : ℕ) where
  rel : ∀ {u v : V}, G.Walk u v → G.Walk u v → Prop
  refl : ∀ {u v : V} (p : G.Walk u v), rel p p
  symm : ∀ {u v : V} {p q : G.Walk u v}, rel p q → rel q p
  trans : ∀ {u v : V} {p q r : G.Walk u v}, rel p q → rel q r → rel p r
  append_left : ∀ {w u v : V} (r : G.Walk w u) {p q : G.Walk u v}, rel p q →
    rel (r.append p) (r.append q)
  append_right : ∀ {u v w : V} {p q : G.Walk u v}, rel p q → ∀ (r : G.Walk v w),
    rel (p.append r) (q.append r)
  two_le : 2 ≤ L
  short : ∀ {u : V} (c : G.Walk u u), c.length ≤ L → rel c .nil

namespace ShortCongr

variable {L : ℕ} (S : ShortCongr G L)

theorem rel_append_reverse {u v : V} (p : G.Walk u v) : S.rel (p.append p.reverse) .nil := by
  induction p with
  | nil => exact S.refl _
  | @cons a b c h p ih =>
    rw [Walk.reverse_cons, Walk.cons_append, Walk.append_assoc]
    have h₁ := S.append_left (.cons h .nil) (S.append_right ih (.cons h.symm .nil))
    simp only [Walk.cons_append, Walk.nil_append] at h₁
    exact S.trans h₁ (S.short (.cons h (.cons h.symm .nil)) (by simpa using S.two_le))

theorem rel_reverse_append {u v : V} (p : G.Walk u v) : S.rel (p.reverse.append p) .nil := by
  simpa using S.rel_append_reverse p.reverse

theorem rel_of_append_reverse {u v : V} {p q : G.Walk u v}
    (h : S.rel (p.append q.reverse) .nil) : S.rel p q := by
  have h₁ : S.rel (p.append (q.reverse.append q)) p := by
    simpa using S.append_left p (S.rel_reverse_append q)
  have h₂ : S.rel ((p.append q.reverse).append q) q := by
    simpa using S.append_right h q
  rw [← Walk.append_assoc] at h₂
  exact S.trans (S.symm h₁) h₂

theorem rel_of_length_add_le {u v : V} (p q : G.Walk u v) (h : p.length + q.length ≤ L) :
    S.rel p q :=
  S.rel_of_append_reverse (S.short _ (by simpa using h))

end ShortCongr

def ShortCongr.ofHomotopic {L : ℕ} (hL : 2 ≤ L)
    (h : ∀ (u : V) (c : G.Walk u u), c.length ≤ L → Homotopic c .nil) : ShortCongr G L where
  rel := Homotopic
  refl := Homotopic.refl
  symm := Homotopic.symm
  trans := Homotopic.trans
  append_left := Homotopic.append_left
  append_right := Homotopic.append_right
  two_le := hL
  short := fun c hc => h _ c hc

namespace ShortCongr

variable {L : ℕ} (S : ShortCongr G L)

theorem shadow (hL : 4 ≤ L) {Γs Φ : Set V} (hdiam : DiamTwo G Φ)
    (hE : ∀ a ∈ Γs, ∀ b ∈ Γs, G.Adj a b →
      ∃ z ∈ Φ, (z = a ∨ G.Adj z a) ∧ (z = b ∨ G.Adj z b))
    {x y : V} (p : G.Walk x y) (hp : ∀ w ∈ p.support, w ∈ Γs) {zy : V} (hzy : zy ∈ Φ)
    (sy : G.Walk y zy) (hsy : sy.length ≤ 1) :
    ∀ {zx : V}, zx ∈ Φ → ∀ (sx : G.Walk zx x), sx.length ≤ 1 →
      ∃ q : G.Walk zx zy, (∀ w ∈ q.support, w ∈ Φ) ∧ S.rel (sx.append (p.append sy)) q := by
  induction p with
  | nil =>
    intro zx hzx sx hsx
    obtain ⟨q, hq, hqΦ⟩ := hdiam.exists_walk hzx hzy
    exact ⟨q, hqΦ, by simpa using S.rel_of_length_add_le (sx.append sy) q (by simp; omega)⟩
  | @cons x x' y h p ih =>
    intro zx hzx sx hsx
    have hx : x ∈ Γs := hp x (by simp)
    have hx' : x' ∈ Γs := hp x' (by simp)
    obtain ⟨z, hzΦ, hz₁, hz₂⟩ := hE x hx x' hx' h
    obtain ⟨s₁, hs₁⟩ := exists_spoke hz₁
    obtain ⟨s', hs'⟩ := exists_spoke hz₂
    obtain ⟨q', hq'Φ, hq'⟩ := ih (fun w hw => hp w (by simp [hw])) sy hsy hzΦ s' hs'
    obtain ⟨q₀, hq₀, hq₀Φ⟩ := hdiam.exists_walk hzx hzΦ
    refine ⟨q₀.append q', fun w hw => ?_, ?_⟩
    · rcases (Walk.mem_support_append_iff _ _).1 hw with hw | hw
      · exact hq₀Φ w hw
      · exact hq'Φ w hw
    · have e₁ : S.rel (Walk.cons h .nil : G.Walk x x') (s₁.reverse.append s') :=
        S.rel_of_length_add_le _ _ (by simp; omega)
      have e₂ : S.rel (sx.append s₁.reverse) q₀ :=
        S.rel_of_length_add_le _ _ (by simp; omega)
      have e₃ := S.append_right e₁ (p.append sy)
      have e₄ := S.append_left s₁.reverse hq'
      have e₅ := S.append_right e₂ q'
      simp only [Walk.cons_append, Walk.nil_append, ← Walk.append_assoc] at e₃ e₄ e₅ ⊢
      refine S.trans (S.append_left sx ?_) e₅
      simpa only [← Walk.append_assoc] using
        S.trans e₃ (by simpa only [← Walk.append_assoc] using e₄)

theorem shadowVertex (hL : 5 ≤ L) {Φ : Set V} (hdiam : DiamTwo G Φ)
    {x y : V} (p : G.Walk x y) (hp : ∀ w ∈ p.support, ∃ z ∈ Φ, z = w ∨ G.Adj z w)
    {zy : V} (hzy : zy ∈ Φ) (sy : G.Walk y zy) (hsy : sy.length ≤ 1) :
    ∀ {zx : V}, zx ∈ Φ → ∀ (sx : G.Walk zx x), sx.length ≤ 1 →
      ∃ q : G.Walk zx zy, (∀ w ∈ q.support, w ∈ Φ) ∧ S.rel (sx.append (p.append sy)) q := by
  induction p with
  | nil =>
    intro zx hzx sx hsx
    obtain ⟨q, hq, hqΦ⟩ := hdiam.exists_walk hzx hzy
    exact ⟨q, hqΦ, by simpa using S.rel_of_length_add_le (sx.append sy) q (by simp; omega)⟩
  | @cons x x' y h p ih =>
    intro zx hzx sx hsx
    obtain ⟨z', hz'Φ, hz'⟩ := hp x' (by simp)
    obtain ⟨s', hs'⟩ := exists_spoke hz'
    obtain ⟨q', hq'Φ, hq'⟩ := ih (fun w hw => hp w (by simp [hw])) sy hsy hz'Φ s' hs'
    obtain ⟨q₀, hq₀, hq₀Φ⟩ := hdiam.exists_walk hzx hz'Φ
    refine ⟨q₀.append q', fun w hw => ?_, ?_⟩
    · rcases (Walk.mem_support_append_iff _ _).1 hw with hw | hw
      · exact hq₀Φ w hw
      · exact hq'Φ w hw
    · have e₁ : S.rel (sx.append (Walk.cons h s'.reverse)) q₀ :=
        S.rel_of_length_add_le _ _ (by simp; omega)
      have key : S.rel (Walk.cons h (p.append sy))
          (Walk.cons h (s'.reverse.append (s'.append (p.append sy)))) := by
        have h1 := S.append_right (S.rel_reverse_append s') (p.append sy)
        have h2 := S.append_left (Walk.cons h .nil) (S.symm h1)
        simpa only [Walk.cons_append, Walk.nil_append, Walk.append_assoc] using h2
      have e₂ := S.append_left sx key
      have e₃ := S.append_right e₁ (s'.append (p.append sy))
      have e₄ := S.append_left q₀ hq'
      simp only [Walk.cons_append, ← Walk.append_assoc] at e₂ e₃ e₄ ⊢
      exact S.trans e₂ (S.trans e₃ e₄)

theorem rel_nil_of_conj {z u : V} (a : G.Walk z u) (p : G.Walk u u)
    (h : S.rel (a.append (p.append a.reverse)) .nil) : S.rel p .nil := by
  have hX : S.rel (a.reverse.append a) .nil := S.rel_reverse_append a
  have h1 := S.append_left a.reverse (S.append_right h a)
  have h2 : S.rel ((a.reverse.append a).append (p.append (a.reverse.append a)))
      (a.reverse.append a) := by
    simpa only [Walk.append_assoc, Walk.nil_append] using h1
  have h3 : S.rel ((a.reverse.append a).append (p.append (a.reverse.append a))) p := by
    have h4 := S.trans (S.append_right hX (p.append (a.reverse.append a)))
      (S.append_left p hX)
    simpa only [Walk.nil_append, Walk.append_nil] using h4
  exact S.trans (S.symm h3) (S.trans h2 hX)

theorem rel_nil_of_shadow (hL : 4 ≤ L) {Γs Φ : Set V} (hdiam : DiamTwo G Φ)
    (hE : ∀ a ∈ Γs, ∀ b ∈ Γs, G.Adj a b →
      ∃ z ∈ Φ, (z = a ∨ G.Adj z a) ∧ (z = b ∨ G.Adj z b))
    (hΦ : ∀ (u : V) (q : G.Walk u u), (∀ w ∈ q.support, w ∈ Φ) → S.rel q .nil)
    {u : V} (p : G.Walk u u) (hp : ∀ w ∈ p.support, w ∈ Γs) : S.rel p .nil := by
  cases p with
  | nil => exact S.refl _
  | @cons _ u' _ h p' =>
    have hspoke : ∃ z ∈ Φ, ∃ s : G.Walk z u, s.length ≤ 1 := by
      by_cases hu : u ∈ Φ
      · exact ⟨u, hu, .nil, by simp⟩
      · obtain ⟨z, hzΦ, hz₁, -⟩ := hE u (hp u (by simp)) u' (hp u' (by simp)) h
        have hz₁' : G.Adj z u := hz₁.resolve_left fun hzu => hu (hzu ▸ hzΦ)
        exact ⟨z, hzΦ, .cons hz₁' .nil, by simp⟩
    obtain ⟨z, hzΦ, s, hs⟩ := hspoke
    obtain ⟨q, hqΦ, hq⟩ := S.shadow hL hdiam hE (.cons h p') hp hzΦ s.reverse (by simpa using hs)
      hzΦ s hs
    exact S.rel_nil_of_conj s _ (S.trans hq (hΦ z q hqΦ))

end ShortCongr

theorem inducedNull_of_diamTwo {Γs Φ : Set V} (hdiam : DiamTwo G Φ)
    (hE : ∀ a ∈ Γs, ∀ b ∈ Γs, G.Adj a b →
      ∃ z ∈ Φ, (z = a ∨ G.Adj z a) ∧ (z = b ∨ G.Adj z b))
    (h4 : ∀ (u : V) (c : G.Walk u u), c.length ≤ 4 → Homotopic c .nil)
    (hΦ : InducedNull G Φ) : InducedNull G Γs :=
  fun _ p hp => (ShortCongr.ofHomotopic (L := 4) (by norm_num) h4).rel_nil_of_shadow
    le_rfl hdiam hE (fun u q hq => hΦ u q hq) p hp

@[expose] def closedNbhd (G : SimpleGraph V) (c : V) : Set V :=
  {y | y = c ∨ G.Adj y c}

theorem diamTwo_closedNbhd (c : V) : DiamTwo G (closedNbhd G c) := by
  intro x hx y hy
  rcases hx with rfl | hxc
  · rcases hy with rfl | hyc
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hyc.symm)
  · rcases hy with rfl | hyc
    · exact Or.inr (Or.inl hxc)
    · by_cases hxy : x = y
      · exact Or.inl hxy
      · exact Or.inr (Or.inr ⟨c, Or.inl rfl, hxc, hyc.symm⟩)

theorem inducedNull_closedNbhd (c : V) : InducedNull G (closedNbhd G c) :=
  fun _ p hp => homotopic_nil_of_forall_adj_or_eq p hp

theorem exists_nbhd_of_cone_cover {c a b : V} (hab : G.Adj a b)
    (h : (a = c ∨ G.Adj a c) ∨ (b = c ∨ G.Adj b c) ∨ ∃ w, G.Adj w c ∧ G.Adj w a ∧ G.Adj w b) :
    ∃ z ∈ closedNbhd G c, (z = a ∨ G.Adj z a) ∧ (z = b ∨ G.Adj z b) := by
  rcases h with ha | hb | ⟨w, hwc, hwa, hwb⟩
  · exact ⟨a, ha, Or.inl rfl, Or.inr hab⟩
  · exact ⟨b, hb, Or.inr hab.symm, Or.inl rfl⟩
  · exact ⟨w, Or.inr hwc, Or.inr hwa, Or.inr hwb⟩

theorem inducedNull_of_cone_cover (c : V) {Γs : Set V}
    (hE : ∀ a ∈ Γs, ∀ b ∈ Γs, G.Adj a b → (a = c ∨ G.Adj a c) ∨ (b = c ∨ G.Adj b c) ∨
      ∃ w, G.Adj w c ∧ G.Adj w a ∧ G.Adj w b)
    (h4 : ∀ (u : V) (c : G.Walk u u), c.length ≤ 4 → Homotopic c .nil) : InducedNull G Γs :=
  inducedNull_of_diamTwo (diamTwo_closedNbhd c)
    (fun a ha b hb hab => exists_nbhd_of_cone_cover hab (hE a ha b hb hab)) h4
    (inducedNull_closedNbhd c)

theorem inducedNull_of_pentagons {Φ : Set V} (hdiam : DiamTwo G Φ)
    (h4 : ∀ (u : V) (c : G.Walk u u), c.length ≤ 4 → Homotopic c .nil)
    (h5 : ∀ (u : V) (c : G.Walk u u), c.IsCycle → c.length = 5 → (∀ x ∈ c.support, x ∈ Φ) →
      Homotopic c .nil) : InducedNull G Φ := by
  refine fun u c hc => homotopic_nil_of_shorten Φ 2 (fun {u v} p hp hpΦ => ?_)
    (fun c hc _ => homotopic_nil_of_length_le_three c (by omega)) c hc
  obtain ⟨q, hq, hqΦ⟩ := hdiam.exists_walk (hpΦ _ p.start_mem_support) (hpΦ _ p.end_mem_support)
  refine ⟨q, hq, hqΦ, homotopic_iff_append_reverse_nil.2 ?_⟩
  refine homotopic_nil_of_forall_isCycle_supp Φ (L := 5) (fun x c hc hlen hΦc => ?_) _
    (by simp; omega) (fun w hw => ?_)
  · rcases Nat.lt_or_ge c.length 5 with hlt | hge
    · exact h4 x c (by omega)
    · exact h5 x c hc (by omega) hΦc
  · rcases (Walk.mem_support_append_iff _ _).1 hw with hw | hw
    · exact hpΦ w hw
    · exact hqΦ w (by simpa using hw)

theorem homotopic_pentagon_nil_of_inner_cycle {Φ : Set V} {x₀ x₁ x₂ x₃ x₄ : V}
    (h₀₁ : G.Adj x₀ x₁) (h₁₂ : G.Adj x₁ x₂) (h₂₃ : G.Adj x₂ x₃) (h₃₄ : G.Adj x₃ x₄)
    (h₄₀ : G.Adj x₄ x₀) (a : G.Walk x₀ x₂) (ha : a.length ≤ 2) (haΦ : ∀ w ∈ a.support, w ∈ Φ)
    (b : G.Walk x₃ x₀) (hb : b.length ≤ 2) (hbΦ : ∀ w ∈ b.support, w ∈ Φ)
    (hΦ : InducedNull G Φ) (h4 : ∀ (u : V) (c : G.Walk u u), c.length ≤ 4 → Homotopic c .nil) :
    Homotopic (.cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil)))) : G.Walk x₀ x₀)
      .nil := by
  have e₁ : Homotopic (.cons h₀₁ (.cons h₁₂ .nil) : G.Walk x₀ x₂) a :=
    homotopic_iff_append_reverse_nil.2 (h4 _ _ (by simp; omega))
  have e₂ : Homotopic (.cons h₃₄ (.cons h₄₀ .nil) : G.Walk x₃ x₀) b :=
    homotopic_iff_append_reverse_nil.2 (h4 _ _ (by simp; omega))
  have e₃ : Homotopic (a.append (.cons h₂₃ b)) .nil := by
    refine hΦ _ _ fun w hw => ?_
    rcases (Walk.mem_support_append_iff _ _).1 hw with hw | hw
    · exact haΦ w hw
    · rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact haΦ _ a.end_mem_support
      · exact hbΦ w hw
  have e₄ := e₁.append ((Homotopic.refl (.cons h₂₃ .nil : G.Walk x₂ x₃)).append e₂)
  simp only [Walk.cons_append, Walk.nil_append] at e₄
  exact e₄.trans e₃

theorem homotopic_short_of_cone (h5 : ∀ (u : V) (c : G.Walk u u), c.length ≤ 5 → Homotopic c .nil)
    (b : V) {x y : V} (p : G.Walk x y)
    (hp : ∀ w ∈ p.support, ∃ z ∈ closedNbhd G b, z = w ∨ G.Adj z w)
    (hx : ∀ z ∈ closedNbhd G b, ∃ r : G.Walk x z, r.length ≤ 2) :
    ∃ q : G.Walk x y, q.length ≤ 3 ∧ Homotopic p q := by
  obtain ⟨z₀, hz₀Φ, hz₀⟩ := hp x p.start_mem_support
  obtain ⟨z₄, hz₄Φ, hz₄⟩ := hp y p.end_mem_support
  obtain ⟨s₀, hs₀⟩ := exists_spoke hz₀
  obtain ⟨s₄, hs₄⟩ := exists_spoke hz₄
  obtain ⟨σ₀, hσ₀⟩ := exists_spoke (hz₀Φ.imp Eq.symm SimpleGraph.Adj.symm)
  obtain ⟨σ₄, hσ₄⟩ := exists_spoke (hz₄Φ.imp Eq.symm SimpleGraph.Adj.symm)
  obtain ⟨q, hqΦ, hq⟩ := (ShortCongr.ofHomotopic (L := 5) (by norm_num) h5).shadowVertex le_rfl
    (diamTwo_closedNbhd b) p hp hz₄Φ s₄.reverse (by simpa using hs₄) hz₀Φ s₀ hs₀
  have hcone : Homotopic q (σ₀.reverse.append σ₄) :=
    homotopic_cone_spokes q (fun w hw => hqΦ w hw) σ₀ hσ₀ σ₄ hσ₄
  have h₁ : Homotopic (s₀.append (p.append s₄.reverse)) (σ₀.reverse.append σ₄) := hq.trans hcone
  have h₂ : Homotopic p (s₀.reverse.append ((σ₀.reverse.append σ₄).append s₄)) := by
    have h₃ := (h₁.append_right s₄).append_left s₀.reverse
    have h₄ : Homotopic p (s₀.reverse.append ((s₀.append (p.append s₄.reverse)).append s₄)) := by
      have e₀ : Homotopic (s₀.reverse.append s₀) .nil := homotopic_reverse_append s₀
      have e₁ : Homotopic (s₄.reverse.append s₄) .nil := homotopic_reverse_append s₄
      have := (e₀.append (Homotopic.refl p)).append e₁
      simp only [Walk.nil_append, Walk.append_nil, Walk.append_assoc] at this ⊢
      simpa only [Walk.append_assoc] using this.symm
    exact h₄.trans h₃
  obtain ⟨r, hr⟩ := hx z₄ hz₄Φ
  have h₅ : Homotopic (s₀.reverse.append (σ₀.reverse.append σ₄)) r :=
    homotopic_of_length_add_le h5 _ _ (by simp; omega)
  refine ⟨r.append s₄, by simp; omega, h₂.trans ?_⟩
  have := h₅.append_right s₄
  simpa only [Walk.append_assoc] using this

end CFSG.Monster.Tri
