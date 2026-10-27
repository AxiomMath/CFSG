module

public import CFSG.Quasithin.Recognition.F4Basic

public section

namespace CFSG.Quasithin.H13.F45Ru

open CFSG.Quasithin

universe u

variable {V : Type u} {Γ : SimpleGraph V}

structure Layers (Γ : SimpleGraph V) (m : ℕ) (b : V) (lay : V → ℕ) : Prop where
  root : lay b = 0
  le : ∀ x, lay x ≤ m
  parent : ∀ x, x ≠ b → ∃ y, Γ.Adj x y ∧ lay y + 1 = lay x
  lip : ∀ x y, Γ.Adj x y → lay y ≤ lay x + 1
  uniq : ∀ x y z, 1 ≤ lay x → lay x < m → Γ.Adj x y → Γ.Adj x z → lay y + 1 = lay x →
    lay z + 1 = lay x → y = z

namespace Layers

variable {m : ℕ} {b : V} {lay : V → ℕ}

theorem lay_le_length (h : Layers Γ m b lay) {x y : V} (w : Γ.Walk x y) :
    lay y ≤ lay x + w.length := by
  induction w with
  | nil => simp
  | @cons x x' y hxx' w ih =>
    have := h.lip x x' hxx'
    rw [SimpleGraph.Walk.length_cons]
    omega

theorem exists_walk (h : Layers Γ m b lay) :
    ∀ (n : ℕ) (x : V), lay x = n → ∃ w : Γ.Walk b x, w.length = n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have hxb : x = b := by
      by_contra hne
      obtain ⟨y, -, hy⟩ := h.parent x hne
      omega
    subst hxb
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ n ih =>
    intro x hx
    have hne : x ≠ b := by
      intro hxb
      subst hxb
      have := h.root
      omega
    obtain ⟨y, hxy, hy⟩ := h.parent x hne
    obtain ⟨w, hw⟩ := ih y (by omega)
    exact ⟨w.concat hxy.symm, by simp [hw]⟩

theorem reachable (h : Layers Γ m b lay) (x : V) : Γ.Reachable b x := by
  obtain ⟨w, -⟩ := h.exists_walk _ x rfl
  exact ⟨w⟩

theorem dist_eq (h : Layers Γ m b lay) (x : V) : Γ.dist b x = lay x := by
  obtain ⟨w, hw⟩ := h.exists_walk _ x rfl
  have h1 : Γ.dist b x ≤ lay x := hw ▸ SimpleGraph.dist_le w
  obtain ⟨w', hw'⟩ := (h.reachable x).exists_walk_length_eq_dist
  have h2 := h.lay_le_length w'
  rw [h.root, hw'] at h2
  omega

theorem smul {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ] (g : H)
    (h : Layers Γ m b lay) : Layers Γ m (g • b) (fun x => lay (g⁻¹ • x)) where
  root := by simpa using h.root
  le x := h.le _
  parent x hx := by
    have hne : g⁻¹ • x ≠ b := fun e => hx (by rw [← e, smul_inv_smul])
    obtain ⟨y, hy, hl⟩ := h.parent _ hne
    refine ⟨g • y, ?_, by simpa using hl⟩
    have := (GraphAction.adj_smul g (g⁻¹ • x) y).mpr hy
    simpa using this
  lip x y hxy := h.lip _ _ ((GraphAction.adj_smul g⁻¹ x y).mpr hxy)
  uniq x y z h1 h2 hxy hxz hy hz := by
    have := h.uniq (g⁻¹ • x) (g⁻¹ • y) (g⁻¹ • z) h1 h2
      ((GraphAction.adj_smul g⁻¹ x y).mpr hxy) ((GraphAction.adj_smul g⁻¹ x z).mpr hxz) hy hz
    exact smul_left_cancel g⁻¹ this

end Layers

theorem uniqueGeod_of_layers {m : ℕ} (hconn : Γ.Connected)
    (hL : ∀ x : V, ∃ lay, Layers Γ m x lay) : UniqueGeod Γ m := by
  intro n p q hp hq h0 hn hnm
  obtain ⟨lay, hl⟩ := hL (p 0)
  have hdp : ∀ i ≤ n, lay (p i) = i := fun i hi => by
    rw [← hl.dist_eq]
    exact GPath.dist_prefix hconn p hp hi
  have hdq : ∀ i ≤ n, lay (q i) = i := fun i hi => by
    rw [← hl.dist_eq, h0]
    exact GPath.dist_prefix hconn q hq hi
  have key : ∀ k, k ≤ n → p (n - k) = q (n - k) := by
    intro k
    induction k with
    | zero => intro _; simpa using hn
    | succ k ih =>
      intro hk
      have e1 := ih (by omega)
      have hi : n - k = (n - (k + 1)) + 1 := by omega
      rw [hi] at e1
      have a1 : Γ.Adj (p (n - (k + 1)) ) (p (n - (k + 1) + 1)) := p.adj _ (by omega)
      have a2 : Γ.Adj (q (n - (k + 1))) (q (n - (k + 1) + 1)) := q.adj _ (by omega)
      rw [e1] at a1
      refine hl.uniq (q (n - (k + 1) + 1)) (p (n - (k + 1))) (q (n - (k + 1))) ?_ ?_
        a1.symm a2.symm ?_ ?_
      · rw [hdq _ (by omega)]
        omega
      · rw [hdq _ (by omega)]
        omega
      · rw [hdp _ (by omega), hdq _ (by omega)]
      · rw [hdq _ (by omega), hdq _ (by omega)]
  refine GPath.ext' fun i hi => ?_
  have := key (n - i) (by omega)
  rwa [Nat.sub_sub_self hi] at this

theorem isGenPolygon_of_layers {m : ℕ} (hm : 2 ≤ m) [Nonempty V] (c : V → Bool)
    (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) (hL : ∀ x : V, ∃ lay, Layers Γ m x lay)
    (hfar : ∃ (u : V) (lay : V → ℕ) (v : V), Layers Γ m u lay ∧ lay v = m)
    (z : ℕ → V) (hadj : ∀ i, Γ.Adj (z i) (z (i + 1))) (hnb : ∀ i, z i ≠ z (i + 2))
    (hper : ∀ i, z (i + 2 * m) = z i) (hval : ∀ v, 2 ≤ (Γ.neighborSet v).encard) :
    IsGenPolygon Γ m := by
  have hconn : Γ.Connected :=
    { preconnected := fun u v => by
        obtain ⟨lay, hl⟩ := hL u
        exact hl.reachable v }
  have hU : UniqueGeod Γ m := uniqueGeod_of_layers hconn hL
  refine ⟨hconn, ⟨c, hc⟩, fun u v => ?_, ?_, hU, ⟨Set.range z, ?_⟩, hval⟩
  · obtain ⟨lay, hl⟩ := hL u
    rw [hl.dist_eq]
    exact hl.le v
  · obtain ⟨u, lay, v, hl, hv⟩ := hfar
    exact ⟨u, v, by rw [hl.dist_eq, hv]⟩
  · exact GPath.isPolygon_of_periodic hconn hc hm hU z hadj hnb hper

theorem layers_of_cover {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ] {m : ℕ}
    {b₁ b₂ : V} {l₁ l₂ : V → ℕ} (h₁ : Layers Γ m b₁ l₁) (h₂ : Layers Γ m b₂ l₂)
    (hcov : ∀ x : V, ∃ g : H, g • b₁ = x ∨ g • b₂ = x) (x : V) :
    ∃ lay, Layers Γ m x lay := by
  obtain ⟨g, hg | hg⟩ := hcov x
  · exact ⟨_, hg ▸ h₁.smul g⟩
  · exact ⟨_, hg ▸ h₂.smul g⟩

end CFSG.Quasithin.H13.F45Ru
