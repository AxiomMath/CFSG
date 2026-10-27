module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_far (F : FanTree Γ G) (u w : V) (n : ℕ) :
    ∃ v, Γ.dist u v = n ∧ Γ.dist w v = Γ.dist w u + n := by
  obtain ⟨P, hP0, hPn⟩ := IsTree.exists_arc_between F.isTree w u
  obtain ⟨Q, hQ⟩ := exists_extend F P (Γ.dist w u + n) (Nat.le_add_right _ _)
  refine ⟨Q.vert (Γ.dist w u + n), ?_, ?_⟩
  · have := Arc.dist_vert F.isTree Q (i := Γ.dist w u) (j := Γ.dist w u + n)
      (Nat.le_add_right _ _) le_rfl
    rw [hQ _ le_rfl, hPn] at this
    rw [this]
    omega
  · have := Arc.dist_eq F.isTree Q (Γ.dist w u + n) le_rfl
    rw [hQ 0 (Nat.zero_le _), hP0] at this
    exact this

theorem exists_adj_ne₂ (F : FanTree Γ G) (v a b : V) : ∃ u, Γ.Adj v u ∧ u ≠ a ∧ u ≠ b := by
  by_contra h
  push Not at h
  have h3 : 3 ≤ Nat.card (Γ.neighborSet v) := by rcases F.valence v with h | h <;> omega
  have hsub : Γ.neighborSet v ⊆ {a, b} := by
    intro u hu
    by_cases hua : u = a
    · exact Or.inl hua
    · exact Or.inr (h u hu hua)
  have hc : (Γ.neighborSet v).ncard ≤ 2 := by
    calc (Γ.neighborSet v).ncard ≤ ({a, b} : Set V).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
        refine (Set.ncard_insert_le a {b}).trans ?_
        rw [Set.ncard_singleton]
  rw [← Nat.card_coe_set_eq] at hc
  omega

theorem eq_of_ball_subset (F : FanTree Γ G) {a b : V} {n : ℕ}
    (h : ∀ v, Γ.dist a v ≤ n → Γ.dist b v ≤ n) : a = b := by
  obtain ⟨v, hv1, hv2⟩ := exists_far F a b n
  have h1 := h v (le_of_eq hv1)
  by_contra hne
  have hpos := F.isTree.connected.pos_dist_of_ne (Ne.symm hne)
  omega

theorem dist_even (F : FanTree Γ G) {a b : V} (ha : Fan86.valence Γ a = 5)
    (hb : Fan86.valence Γ b = 5) : Γ.dist a b % 2 = 0 := by
  by_contra h
  have h1 := valence_of_dist_odd F ha (by omega : Γ.dist a b % 2 = 1)
  omega

end P71

end CFSG.Quasithin.Fan86
