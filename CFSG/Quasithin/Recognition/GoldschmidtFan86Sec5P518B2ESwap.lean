module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2ERot
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def EMoves (Γ : SimpleGraph V) (q : G) (v β : V) : Prop :=
  ∃ w, Γ.Adj β w ∧ w ≠ v ∧ q • w ≠ w

theorem eDist_le_two {v β w : V} (h1 : Γ.Adj v β) (h2 : Γ.Adj β w) : Γ.dist v w ≤ 2 := by
  have := SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 .nil))
  simpa using this

theorem eExists_mid (F : FanTree Γ G) {v w : V} (h : Γ.dist v w = 2) :
    ∃ u, Γ.Adj v u ∧ Γ.Adj u w := by
  obtain ⟨p, hp⟩ := F.isTree.connected.exists_walk_length_eq_dist v w
  rw [h] at hp
  cases p with
  | nil => simp at hp
  | cons h1 p' =>
    cases p' with
    | nil => simp at hp
    | cons h2 p'' =>
      cases p'' with
      | nil => exact ⟨_, h1, h2⟩
      | cons _ _ => simp at hp

theorem eMoves_smul (F : FanTree Γ G) {v β : V} {x q : G} (hx : x • v = v)
    (hβ : Γ.Adj v β) (h : x * q * x⁻¹ * q⁻¹ ∈ ballStab Γ G 2 v) (hm : EMoves Γ q v β) :
    EMoves Γ q v (x • β) := by
  obtain ⟨w, hβw, hwv, hqw⟩ := hm
  refine ⟨x • w, (F.adj_smul x β w).2 hβw, ?_, ?_⟩
  · intro hxw
    apply hwv
    have : x • w = x • v := by rw [hxw, hx]
    exact MulAction.injective x this
  · intro hq
    have hd : Γ.dist v (x • w) ≤ 2 := by
      have := dist_smul F x v w
      rw [hx] at this
      rw [this]
      exact eDist_le_two hβ hβw
    have h1 : (x * q * x⁻¹ * q⁻¹) • (x • w) = x • w := h (x • w) hd
    simp only [mul_smul] at h1
    rw [inv_smul_eq_iff.2 hq.symm, inv_smul_smul] at h1
    exact hqw (MulAction.injective x h1)

theorem eMoves_pow (F : FanTree Γ G) {v β : V} {x q : G} (hx : x • v = v)
    (hβ : Γ.Adj v β) (h : x * q * x⁻¹ * q⁻¹ ∈ ballStab Γ G 2 v) (hm : EMoves Γ q v β) (n : ℕ) :
    EMoves Γ q v ((x ^ n) • β) := by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    have hfix : (x ^ n) • v = v := by simpa using eZpow_fix hx (n : ℤ)
    have hadj : Γ.Adj v ((x ^ n) • β) := by
      have := (F.adj_smul (x ^ n) v β).2 hβ
      rwa [hfix] at this
    rw [pow_succ', mul_smul]
    exact eMoves_smul F hx hadj h ih

end P518

end CFSG.Quasithin.Fan86
