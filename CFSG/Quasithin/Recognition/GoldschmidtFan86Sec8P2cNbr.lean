module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo

public section

namespace CFSG.Quasithin.Fan86.P2c

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_adj_of_dist_two (F : FanTree Γ G) {β w : V} (hw : Γ.dist β w = 2) :
    ∃ u, Γ.Adj β u ∧ Γ.Adj u w := by
  obtain ⟨u, huw, hβu⟩ := IsTree.exists_adj_dist_succ F.isTree (u := β) (v := w) (n := 1) hw
  exact ⟨u, SimpleGraph.dist_eq_one_iff_adj.1 hβu, huw⟩

theorem mem_ballStab_two_of (F : FanTree Γ G) {β : V} {g : G} (hgβ : g • β = β)
    (h : ∀ u, Γ.Adj β u → g • u = u ∧ g ∈ nbrStab Γ G u) : g ∈ ballStab Γ G 2 β := by
  refine mem_ballStab.2 fun w hw => ?_
  have hd : Γ.dist β w = 0 ∨ Γ.dist β w = 1 ∨ Γ.dist β w = 2 := by omega
  rcases hd with h0 | h1 | h2
  · have := F.isTree.connected.dist_eq_zero_iff.1 h0
    subst this
    exact hgβ
  · exact (h w (SimpleGraph.dist_eq_one_iff_adj.1 h1)).1
  · obtain ⟨u, hβu, huw⟩ := exists_adj_of_dist_two F h2
    exact mem_nbrStab.1 (h u hβu).2 w huw

theorem mem_nbrStab_of_comm (F : FanTree Γ G) {a t : V} {y g : G} (hy : y • a = t)
    (hc : g * y = y * g) (hg : g ∈ nbrStab Γ G a) : g ∈ nbrStab Γ G t := by
  refine mem_nbrStab.2 fun w hw => ?_
  have hu : Γ.Adj a (y⁻¹ • w) := by
    have := (F.adj_smul y⁻¹ t w).2 hw
    rwa [← hy, inv_smul_smul] at this
  have hgu := mem_nbrStab.1 hg _ hu
  calc g • w = g • (y • (y⁻¹ • w)) := by rw [smul_inv_smul]
    _ = (g * y) • (y⁻¹ • w) := by rw [mul_smul]
    _ = y • (g • (y⁻¹ • w)) := by rw [hc, mul_smul]
    _ = w := by rw [hgu, smul_inv_smul]

theorem mem_ballStab_smul (F : FanTree Γ G) {n : ℕ} {v : V} {c : G} (g : G)
    (hc : g⁻¹ * c * g ∈ ballStab Γ G n v) : c ∈ ballStab Γ G n (g • v) := by
  refine mem_ballStab.2 fun w hw => ?_
  have hd : Γ.dist v (g⁻¹ • w) ≤ n := by
    have := dist_smul F g⁻¹ (g • v) w
    rw [inv_smul_smul] at this
    omega
  have h1 := mem_ballStab.1 hc _ hd
  calc c • w = c • (g • (g⁻¹ • w)) := by rw [smul_inv_smul]
    _ = g • ((g⁻¹ * c * g) • (g⁻¹ • w)) := by simp [mul_smul]
    _ = w := by rw [h1, smul_inv_smul]

theorem mem_ballStab_three (F : FanTree Γ G) {α : V} {g : G} (hgα : g • α = α)
    (h : ∀ β, Γ.Adj α β → g ∈ ballStab Γ G 2 β) : g ∈ ballStab Γ G 3 α := by
  refine mem_ballStab.2 fun w hw => ?_
  by_cases h0 : Γ.dist α w = 0
  · have := F.isTree.connected.dist_eq_zero_iff.1 h0
    subst this
    exact hgα
  · obtain ⟨d, hd⟩ : ∃ d, Γ.dist α w = d + 1 := ⟨Γ.dist α w - 1, by omega⟩
    rw [SimpleGraph.dist_comm] at hd
    obtain ⟨β, hβα, hwβ⟩ := IsTree.exists_adj_dist_succ F.isTree (u := w) (v := α) (n := d) hd
    refine mem_ballStab.1 (h β hβα.symm) w ?_
    rw [SimpleGraph.dist_comm] at hwβ hd
    omega

end CFSG.Quasithin.Fan86.P2c
