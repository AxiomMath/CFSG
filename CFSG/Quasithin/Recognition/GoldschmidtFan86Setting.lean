module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.QuasithinUnique

variable {V G : Type*} [Group G] [MulAction G V]

structure FanTree (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] : Prop where
  isTree : Γ.IsTree
  adj_smul : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v
  faithful : ∀ g : G, (∀ v : V, g • v = v) → g = 1
  loc_finite : ∀ v : V, Finite (MulAction.stabilizer G v)
  loc_trans : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b → ∃ g ∈ MulAction.stabilizer G v, g • a = b
  valence : ∀ v : V, Nat.card (Γ.neighborSet v) = 3 ∨ Nat.card (Γ.neighborSet v) = 5
  alternating : ∀ u v : V, Γ.Adj u v → Nat.card (Γ.neighborSet u) ≠ Nat.card (Γ.neighborSet v)
  frobenius_two : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b → ∀ g ∈ MulAction.stabilizer G v,
    g • a = a → g • b = b → ∀ c : V, Γ.Adj v c → g • c = c
  frobenius_nonreg : ∀ v a : V, Γ.Adj v a → ∃ g ∈ MulAction.stabilizer G v, g • a = a ∧
    ∃ c : V, Γ.Adj v c ∧ g • c ≠ c
  edge_two : ∀ u v : V, Γ.Adj u v →
    IsPGroup 2 ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G v)
  charTwo : ∀ v : V, CharTwo (MulAction.stabilizer G v)

@[expose] def EdgeTransitive (Γ : SimpleGraph V) (H : Subgroup G) : Prop :=
  ∀ u v u' v' : V, Γ.Adj u v → Γ.Adj u' v' →
    ∃ h ∈ H, (h • u = u' ∧ h • v = v') ∨ (h • u = v' ∧ h • v = u')

namespace FanTree

variable {Γ : SimpleGraph V} (F : FanTree Γ G)
include F

theorem exists_adj (v : V) : ∃ w, Γ.Adj v w := by
  have h : 0 < Nat.card (Γ.neighborSet v) := by
    rcases F.valence v with h | h <;> omega
  obtain ⟨⟨w, hw⟩⟩ := (Nat.card_pos_iff.1 h).1
  exact ⟨w, hw⟩

theorem exists_smul_of_walk_even : ∀ (n : ℕ) {u w : V} (p : Γ.Walk u w), p.length = 2 * n →
    ∃ g : G, g • u = w := by
  intro n
  induction n with
  | zero =>
    intro u w p hp
    obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero (by omega : p.length = 0)
    exact ⟨1, one_smul _ _⟩
  | succ n ih =>
    intro u w p hp
    cases p with
    | nil => simp at hp
    | cons h1 p1 =>
      cases p1 with
      | nil =>
        simp at hp
        omega
      | cons h2 q =>
        obtain ⟨g, hg, hgu⟩ := F.loc_trans _ _ _ h1.symm h2
        obtain ⟨g', hg'⟩ := ih q (by simp at hp; omega)
        exact ⟨g' * g, by rw [mul_smul, hgu, hg']⟩

theorem edgeTransitive : EdgeTransitive Γ (⊤ : Subgroup G) := by
  intro u v u' v' huv hu'v'
  obtain ⟨p⟩ := F.isTree.connected.preconnected u u'
  have key : ∀ (a b a' b' : V), Γ.Adj a b → Γ.Adj a' b' → (∃ g : G, g • a = a') →
      ∃ g : G, g • a = a' ∧ g • b = b' := by
    rintro a b a' b' hab ha'b' ⟨g, hg⟩
    have h1 : Γ.Adj a' (g • b) := by
      have := (F.adj_smul g a b).2 hab
      rwa [hg] at this
    obtain ⟨k, hk, hkb⟩ := F.loc_trans a' _ _ h1 ha'b'
    exact ⟨k * g, by rw [mul_smul, hg, MulAction.mem_stabilizer_iff.1 hk], by
      rw [mul_smul, hkb]⟩
  rcases Nat.even_or_odd p.length with ⟨n, hn⟩ | ⟨n, hn⟩
  · obtain ⟨g, hg⟩ := F.exists_smul_of_walk_even n p (by omega)
    obtain ⟨g', h1, h2⟩ := key u v u' v' huv hu'v' ⟨g, hg⟩
    exact ⟨g', trivial, Or.inl ⟨h1, h2⟩⟩
  · obtain ⟨g, hg⟩ := F.exists_smul_of_walk_even (n + 1) (p.concat hu'v') (by
      rw [SimpleGraph.Walk.length_concat]; omega)
    have hg' : g • u = v' := by simpa using hg
    obtain ⟨g', h1, h2⟩ := key u v v' u' huv hu'v'.symm ⟨g, hg'⟩
    exact ⟨g', trivial, Or.inr ⟨h1, h2⟩⟩

theorem eq_bot_of_edgeTransitive {U : Subgroup G} {α β : V} (hαβ : Γ.Adj α β)
    (hU : ∀ u ∈ U, u • α = α ∧ u • β = β)
    (hN : EdgeTransitive Γ (Subgroup.normalizer (U : Set G))) : U = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  apply F.faithful
  intro w
  obtain ⟨w', hw'⟩ := F.exists_adj w
  obtain ⟨n, hn, h⟩ := hN α β w w' hαβ hw'
  have hconj : n⁻¹ * u * n ∈ U := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) u).1 hu
    simpa using this
  obtain ⟨h1, h2⟩ := hU _ hconj
  have hun : u * n = n * (n⁻¹ * u * n) := by simp only [mul_assoc, mul_inv_cancel_left]
  have key : ∀ x y : V, n • α = x → n • β = y → u • x = x ∧ u • y = y := by
    rintro x y rfl rfl
    constructor
    · rw [← mul_smul, hun, mul_smul, h1]
    · rw [← mul_smul, hun, mul_smul, h2]
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact (key _ _ ha hb).1
  · exact (key _ _ ha hb).2

end FanTree

end CFSG.Quasithin.Fan86
