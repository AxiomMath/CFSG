module

public import CFSG.Monster.B.GSide.HomotopyLocal
public import CFSG.YGroups.MarkedWalks
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.B.Recog CFSG.Monster.B.GSide CFSG.YGroups

variable {V : Type*} {G : SimpleGraph V}

theorem exists_closed_walk_four {u : V} (c : G.Walk u u) (hc : c.length = 4) :
    ∃ (x₁ x₂ x₃ : V) (h₀₁ : G.Adj u x₁) (h₁₂ : G.Adj x₁ x₂) (h₂₃ : G.Adj x₂ x₃)
      (h₃₀ : G.Adj x₃ u), c = .cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₀ .nil))) := by
  cases c with
  | nil => simp at hc
  | cons h₀₁ c =>
    cases c with
    | nil => simp at hc
    | cons h₁₂ c =>
      cases c with
      | nil => simp at hc
      | cons h₂₃ c =>
        cases c with
        | nil => simp at hc
        | cons h₃₀ c =>
          cases c with
          | nil => exact ⟨_, _, _, h₀₁, h₁₂, h₂₃, h₃₀, rfl⟩
          | cons _ _ => simp at hc

theorem exists_closed_walk_five {u : V} (c : G.Walk u u) (hc : c.length = 5) :
    ∃ (x₁ x₂ x₃ x₄ : V) (h₀₁ : G.Adj u x₁) (h₁₂ : G.Adj x₁ x₂) (h₂₃ : G.Adj x₂ x₃)
      (h₃₄ : G.Adj x₃ x₄) (h₄₀ : G.Adj x₄ u),
      c = .cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil)))) := by
  cases c with
  | nil => simp at hc
  | cons h₀₁ c =>
    cases c with
    | nil => simp at hc
    | cons h₁₂ c =>
      cases c with
      | nil => simp at hc
      | cons h₂₃ c =>
        cases c with
        | nil => simp at hc
        | cons h₃₄ c =>
          cases c with
          | nil => simp at hc
          | cons h₄₀ c =>
            cases c with
            | nil => exact ⟨_, _, _, _, h₀₁, h₁₂, h₂₃, h₃₄, h₄₀, rfl⟩
            | cons _ _ => simp at hc

theorem exists_walk_four {u v : V} (c : G.Walk u v) (hc : c.length = 4) :
    ∃ (x₁ x₂ x₃ : V) (h₀₁ : G.Adj u x₁) (h₁₂ : G.Adj x₁ x₂) (h₂₃ : G.Adj x₂ x₃)
      (h₃₄ : G.Adj x₃ v), c = .cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ .nil))) := by
  cases c with
  | nil => simp at hc
  | cons h₀₁ c =>
    cases c with
    | nil => simp at hc
    | cons h₁₂ c =>
      cases c with
      | nil => simp at hc
      | cons h₂₃ c =>
        cases c with
        | nil => simp at hc
        | cons h₃₄ c =>
          cases c with
          | nil => exact ⟨_, _, _, h₀₁, h₁₂, h₂₃, h₃₄, rfl⟩
          | cons _ _ => simp at hc

theorem dist_eq_two_of_adj_adj {x y w : V} (hne : x ≠ y) (hna : ¬G.Adj x y) (h₁ : G.Adj x w)
    (h₂ : G.Adj w y) : G.dist x y = 2 := by
  have hr : G.Reachable x y := (h₁.reachable.trans h₂.reachable)
  have h₃ : G.dist x y ≤ 2 := (SimpleGraph.dist_le (Walk.cons h₁ (Walk.cons h₂ Walk.nil)))
  have h₄ := hr.one_lt_dist_of_ne_of_not_adj hne hna
  omega

theorem dist_eq_two_iff {x y : V} :
    G.dist x y = 2 ↔ x ≠ y ∧ ¬G.Adj x y ∧ ∃ w, G.Adj x w ∧ G.Adj w y := by
  refine ⟨fun h => ?_, fun ⟨hne, hna, w, h₁, h₂⟩ => dist_eq_two_of_adj_adj hne hna h₁ h₂⟩
  have hr : G.Reachable x y := by
    by_contra hn
    have : G.dist x y = 0 := by simp [hn]
    omega
  refine ⟨fun hxy => ?_, fun hxy => ?_, ?_⟩
  · subst hxy
    simp at h
  · rw [← SimpleGraph.dist_eq_one_iff_adj] at hxy
    omega
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    rw [h] at hp
    cases p with
    | nil => simp at hp
    | cons h₁ p =>
      cases p with
      | nil => simp at hp
      | cons h₂ p =>
        cases p with
        | nil => exact ⟨_, h₁, h₂⟩
        | cons _ _ => simp at hp

theorem homotopic_nil_of_length_le_four_of_mu
    (hμ : ∀ x y : V, G.dist x y = 2 → (G.induce (G.commonNeighbors x y)).Preconnected)
    {u : V} (c : G.Walk u u) (hc : c.length ≤ 4) : Homotopic c .nil := by
  rcases Nat.lt_or_ge c.length 4 with hlt | hge
  · exact homotopic_nil_of_length_le_three c (by omega)
  · obtain ⟨x₁, x₂, x₃, h₀₁, h₁₂, h₂₃, h₃₀, rfl⟩ := exists_closed_walk_four c (by omega)
    by_cases hx : u = x₂ ∨ G.Adj u x₂
    · refine homotopic_nil_of_forall_adj_or_eq (z := u) _ fun w hw => ?_
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr h₀₁.symm
      · rcases hx with hx | hx
        · exact Or.inl hx.symm
        · exact Or.inr hx.symm
      · exact Or.inr h₃₀
      · exact Or.inl rfl
    · push Not at hx
      have hd := dist_eq_two_of_adj_adj hx.1 hx.2 h₀₁ h₁₂
      exact homotopic_quadrangle_nil_of_preconnected (hμ _ _ hd) h₀₁ h₁₂ h₂₃ h₃₀

structure CommStruct {V : Type*} (Γ : SimpleGraph V) (I : Type*) where
  ι : V → I
  cen : I → V → Prop
  Z : Set I
  Qs : I → Set V
  mid : V → V → V
  three : V → V → Prop
  cen_symm : ∀ x y, cen (ι x) y → cen (ι y) x
  cen_refl : ∀ x, cen (ι x) x
  cen_of_adj : ∀ x y, Γ.Adj x y → cen (ι x) y
  adj_mid : ∀ x y, Γ.Adj x y → Γ.Adj x (mid x y) ∧ Γ.Adj y (mid x y)
  inv_cases : ∀ i, (∃ x, ι x = i) ∨ i ∈ Z

structure ASegHyp0 {V : Type*} {Γ : SimpleGraph V} {I : Type*} (A : CommStruct Γ I) : Prop where
  h88 : ∀ (u : V) (c : Γ.Walk u u), c.length ≤ 4 → Homotopic c .nil
  h85 : ∀ x a b : V, A.cen (A.ι x) a → A.cen (A.ι x) b → Γ.Adj a b →
    (a = x ∨ Γ.Adj a x) ∨ (b = x ∨ Γ.Adj b x) ∨ ∃ c, Γ.Adj c x ∧ Γ.Adj c a ∧ Γ.Adj c b
  h87_1 : ∀ z ∈ A.Z, ∀ x ∈ A.Qs z, ∀ y ∈ A.Qs z,
    x = y ∨ Γ.Adj x y ∨ ∃ w ∈ A.Qs z, Γ.Adj x w ∧ Γ.Adj w y
  h87_3 : ∀ z ∈ A.Z, ∀ x ∈ A.Qs z, ∀ y ∈ A.Qs z, ∀ v ∈ A.Qs z, Γ.Adj x y →
    A.cen (A.ι v) x ∨ A.cen (A.ι v) y ∨ A.cen (A.ι v) (A.mid x y)
  h89 : ∀ z ∈ A.Z, ∀ u v : V, A.cen z u → A.cen z v → u ∉ A.Qs z → v ∉ A.Qs z → Γ.Adj u v →
    ∃ w ∈ A.Qs z, Γ.Adj w u ∧ Γ.Adj w v
  h810 : ∀ (i : I) (x y : V), A.cen i x → A.cen i y → Γ.dist x y = 2 → ¬A.cen (A.ι x) y →
    ∃ v, A.cen i v ∧ Γ.Adj v x ∧ Γ.Adj v y
  h83_2 : ∀ x y v : V, Γ.dist x y = 2 → Γ.Adj y v → ∃ i, A.cen i x ∧ A.cen i y ∧ A.cen i v
  h813_1 : ∀ z ∈ A.Z, ∀ x y : V, A.cen z x → A.cen z y →
    (∃ b, A.cen z b ∧ A.cen (A.ι x) b ∧ A.cen (A.ι y) b) ∨ A.three x y
  h814 : ∀ x u : V, (∃ y, (y = u ∨ Γ.Adj y u) ∧ A.cen (A.ι x) y) →
    x = u ∨ Γ.Adj x u ∨ ∃ w, Γ.Adj x w ∧ Γ.Adj w u

structure ASegHyp {V : Type*} {Γ : SimpleGraph V} {I : Type*} (A : CommStruct Γ I) : Prop
    extends ASegHyp0 A where
  h3C : ∀ x y : V, A.three x y → (¬∃ b, A.cen (A.ι x) b ∧ A.cen (A.ι y) b) →
    ∀ p q : Γ.Walk x y, p.length = 3 → q.length = 3 → Homotopic p q
  hS4 : ∀ x u v : V, A.three x u → Γ.Adj u v → ¬(x = v ∨ Γ.Adj x v) →
    (¬∃ w, Γ.Adj x w ∧ Γ.Adj w v) → (¬∃ b, A.cen (A.ι x) b ∧ A.cen (A.ι v) b) →
    ∃ c, Γ.Adj x c ∧ Γ.Adj c (A.mid u v)

end CFSG.Monster.Tri
