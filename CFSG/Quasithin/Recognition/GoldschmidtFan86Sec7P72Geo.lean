module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

namespace P72

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem dist_two (hT : Γ.IsTree) {α ν l : V} (h1 : Γ.Adj α ν) (h2 : Γ.Adj ν l) (hne : l ≠ α) :
    Γ.dist α l = 2 := by
  have h0 : Γ.dist α ν = 1 := dist_eq_one_iff_adj.mpr h1
  have := IsTree.dist_succ_of_ne hT h1.symm h2 hne.symm (by rw [SimpleGraph.dist_self, h0])
  omega

theorem dist_branch (hT : Γ.IsTree) {α ν ν' l l' : V} (h1 : Γ.Adj α ν) (h2 : Γ.Adj ν l)
    (hl : l ≠ α) (h1' : Γ.Adj α ν') (h2' : Γ.Adj ν' l') (hl' : l' ≠ α) (hne : ν ≠ ν') :
    Γ.dist l ν' = 3 ∧ Γ.dist l l' = 4 := by
  have a1 : Γ.dist l ν = 1 := dist_eq_one_iff_adj.mpr h2.symm
  have a2 : Γ.dist l α = 2 := by
    have := IsTree.dist_succ_of_ne hT h2 h1.symm hl (by rw [SimpleGraph.dist_self, a1])
    omega
  have a3 : Γ.dist l ν' = 3 := by
    have := IsTree.dist_succ_of_ne hT h1 h1' hne (by rw [a1, a2])
    omega
  refine ⟨a3, ?_⟩
  have := IsTree.dist_succ_of_ne hT h1'.symm h2' hl'.symm (by rw [a2, a3])
  omega

theorem dist_arc4 (hT : Γ.IsTree) {x0 x1 x2 x3 x4 : V} (h01 : Γ.Adj x0 x1) (h12 : Γ.Adj x1 x2)
    (h23 : Γ.Adj x2 x3) (h34 : Γ.Adj x3 x4) (n02 : x0 ≠ x2) (n13 : x1 ≠ x3) (n24 : x2 ≠ x4) :
    Γ.dist x4 x3 = 1 ∧ Γ.dist x4 x2 = 2 ∧ Γ.dist x4 x1 = 3 ∧ Γ.dist x4 x0 = 4 := by
  have a1 : Γ.dist x4 x3 = 1 := dist_eq_one_iff_adj.mpr h34.symm
  have a2 : Γ.dist x4 x2 = 2 := by
    have := IsTree.dist_succ_of_ne hT h34 h23.symm n24.symm (by rw [SimpleGraph.dist_self, a1])
    omega
  have a3 : Γ.dist x4 x1 = 3 := by
    have := IsTree.dist_succ_of_ne hT h23 h12.symm n13.symm (by rw [a1, a2])
    omega
  refine ⟨a1, a2, a3, ?_⟩
  have := IsTree.dist_succ_of_ne hT h12 h01.symm n02.symm (by rw [a2, a3])
  omega

theorem dist_arc4_ext (hT : Γ.IsTree) {x0 x1 x2 x3 x4 ν : V} (h01 : Γ.Adj x0 x1)
    (h12 : Γ.Adj x1 x2) (h23 : Γ.Adj x2 x3) (h34 : Γ.Adj x3 x4) (n02 : x0 ≠ x2) (n13 : x1 ≠ x3)
    (n24 : x2 ≠ x4) (hν : Γ.Adj x0 ν) (hne : x1 ≠ ν) : Γ.dist x4 ν = 5 := by
  obtain ⟨-, -, a3, a4⟩ := dist_arc4 hT h01 h12 h23 h34 n02 n13 n24
  have := IsTree.dist_succ_of_ne hT h01 hν hne (by rw [a3, a4])
  omega

theorem val_arc4 (F : FanTree Γ G) {x0 x1 x2 x3 x4 : V} (h01 : Γ.Adj x0 x1)
    (h12 : Γ.Adj x1 x2) (h23 : Γ.Adj x2 x3) (h34 : Γ.Adj x3 x4) (h0 : valence Γ x0 = 5) :
    valence Γ x1 = 3 ∧ valence Γ x2 = 5 ∧ valence Γ x3 = 3 ∧ valence Γ x4 = 5 := by
  have v1 := valence_adj_three F h0 h01
  have v2 := valence_adj_five F v1 h12
  have v3 := valence_adj_three F v2 h23
  exact ⟨v1, v2, v3, valence_adj_five F v3 h34⟩

theorem nbrSet_eq_three {β a b c : V} (hβ : valence Γ β = 3) (ha : Γ.Adj β a) (hb : Γ.Adj β b)
    (hc : Γ.Adj β c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Γ.neighborSet β = {a, b, c} := by
  have hcard : (Γ.neighborSet β).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hβ
  have hfin : (Γ.neighborSet β).Finite := Set.finite_of_ncard_pos (by omega)
  have hsub : ({a, b, c} : Set V) ⊆ Γ.neighborSet β := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Set V).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac]) (Set.toFinite _), Set.ncard_pair hbc]
  exact (Set.eq_of_subset_of_ncard_le hsub (by omega) hfin).symm

theorem exists_arc4 (F : FanTree Γ G) (x0 : V) :
    ∃ x1 x2 x3 x4 : V, Γ.Adj x0 x1 ∧ Γ.Adj x1 x2 ∧ Γ.Adj x2 x3 ∧ Γ.Adj x3 x4 ∧ x0 ≠ x2 ∧
      x1 ≠ x3 ∧ x2 ≠ x4 := by
  obtain ⟨x1, h01⟩ := F.exists_adj x0
  obtain ⟨x2, h12, n02⟩ := F.exists_adj_ne x1 x0
  obtain ⟨x3, h23, n13⟩ := F.exists_adj_ne x2 x1
  obtain ⟨x4, h34, n24⟩ := F.exists_adj_ne x3 x2
  exact ⟨x1, x2, x3, x4, h01, h12, h23, h34, n02.symm, n13.symm, n24.symm⟩

end P72

end CFSG.Quasithin.Fan86
