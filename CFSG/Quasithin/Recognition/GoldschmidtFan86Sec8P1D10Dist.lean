module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem beta_injective (F : FanTree Γ G) (h : Fan71c F L) : Function.Injective D.beta := by
  intro i j hij
  by_contra hne
  have hsh : ∀ m, m ≤ 4 → ∀ k, D.x⁻¹ • (D.P k).vert m = (D.P (k + 1)).vert m :=
    fun m hm k => D.x_inv_smul_vert F h k hm
  have hβ : ∀ k, D.beta k = D.beta 0 :=
    fin5_shift_const (g := D.x⁻¹) (fun k => hsh 1 (by norm_num) k) hne hij
  have hα1 : ∀ k, D.alpha k ∈ Γ.neighborSet (D.beta 0) \ {α} := fun k =>
    ⟨by rw [← hβ k]; exact D.adj_beta_alpha k, D.alpha_ne_start k⟩
  have hα2 : (Γ.neighborSet (D.beta 0) \ {α}).ncard < 5 := by
    rw [neighborSet_diff_ncard (D.valence_beta F 0) (D.adj_start_beta 0).symm]
    norm_num
  have hα3 := not_injective_of_ncard_lt
    (Set.Finite.subset (neighborSet_finite (by norm_num) (D.valence_beta F 0)) Set.sdiff_subset)
    hα2 hα1
  obtain ⟨i', j', hij', hne'⟩ := Function.not_injective_iff.1 hα3
  have hα : ∀ k, D.alpha k = D.alpha 0 :=
    fin5_shift_const (g := D.x⁻¹) (fun k => hsh 2 (by norm_num) k) hne' hij'
  have hξ1 : ∀ k, D.xi k ∈ Γ.neighborSet (D.alpha 0) \ {D.beta 0} := fun k =>
    ⟨by rw [← hα k]; exact D.adj_alpha_xi k, by rw [← hβ k]; exact D.xi_ne_beta k⟩
  have hξ2 : (Γ.neighborSet (D.alpha 0) \ {D.beta 0}).ncard < 5 := by
    rw [neighborSet_diff_ncard (D.valence_alpha F 0) (D.adj_beta_alpha 0).symm]
    norm_num
  have hξ3 := not_injective_of_ncard_lt
    (Set.Finite.subset (neighborSet_finite (by norm_num) (D.valence_alpha F 0)) Set.sdiff_subset)
    hξ2 hξ1
  obtain ⟨i'', j'', hij'', hne''⟩ := Function.not_injective_iff.1 hξ3
  have hξ : ∀ k, D.xi k = D.xi 0 :=
    fin5_shift_const (g := D.x⁻¹) (fun k => hsh 3 (by norm_num) k) hne'' hij''
  have hδ1 : ∀ k, D.delta k ∈ Γ.neighborSet (D.xi 0) := fun k => by
    rw [← hξ k]; exact D.adj_xi_delta k
  have hδ2 : (Γ.neighborSet (D.xi 0)).ncard < 5 := by
    rw [neighborSet_ncard (D.valence_xi F 0)]
    norm_num
  exact not_injective_of_ncard_lt (neighborSet_finite (by norm_num) (D.valence_xi F 0)) hδ2 hδ1
    D.delta_injective

theorem dist_vert_ne (F : FanTree Γ G) (h : Fan71c F L) {i j : Fin 5} (hij : i ≠ j) {m m' : ℕ}
    (hm : m ≤ 4) (hm' : m' ≤ 4) :
    Γ.dist ((D.P i).vert m) ((D.P j).vert m') = m + m' := by
  have hb : (D.P i).vert 1 ≠ (D.P j).vert 1 := fun h' => hij (D.beta_injective F h h')
  have hA : ∀ k, k ≤ m → (Arc.rev (Arc.take (D.P i) m hm)).vert k = (D.P i).vert (m - k) :=
    fun k _ => Arc.rev_vert _ k
  have hjn : (Arc.rev (Arc.take (D.P i) m hm)).vert m = (Arc.take (D.P j) m' hm').vert 0 := by
    rw [hA m le_rfl, Nat.sub_self, D.start]
    exact (D.start j).symm
  have hnb : 1 ≤ m → 1 ≤ m' →
      (Arc.rev (Arc.take (D.P i) m hm)).vert (m - 1) ≠ (Arc.take (D.P j) m' hm').vert 1 :=
    fun h1 h2 => by
      rw [hA (m - 1) (by omega), show m - (m - 1) = 1 by omega]
      exact hb
  have hC := Arc.dist_eq F.isTree
    (Arc.append (Arc.rev (Arc.take (D.P i) m hm)) (Arc.take (D.P j) m' hm') hjn hnb) (m + m')
    le_rfl
  rw [Arc.append_vert_le _ _ _ _ (Nat.zero_le m),
    Arc.append_vert_ge _ _ _ _ (Nat.le_add_right m m'), Nat.add_sub_cancel_left,
    hA 0 (Nat.zero_le m), Nat.sub_zero] at hC
  exact hC

theorem dist_arc (F : FanTree Γ G) (i : Fin 5) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 4) :
    Γ.dist ((D.P i).vert a) ((D.P i).vert b) = b - a :=
  Arc.dist_vert F.isTree (D.P i) hab hb

theorem dist_beta_alpha (i : Fin 5) : Γ.dist (D.beta i) (D.alpha i) = 1 :=
  dist_eq_one_iff_adj.2 (D.adj_beta_alpha i)

theorem dist_alpha_xi (i : Fin 5) : Γ.dist (D.alpha i) (D.xi i) = 1 :=
  dist_eq_one_iff_adj.2 (D.adj_alpha_xi i)

theorem dist_beta_xi (F : FanTree Γ G) (i : Fin 5) : Γ.dist (D.beta i) (D.xi i) = 2 :=
  D.dist_arc F i (a := 1) (b := 3) (by norm_num) (by norm_num)

theorem dist_beta_delta (F : FanTree Γ G) (i : Fin 5) : Γ.dist (D.beta i) (D.delta i) = 3 :=
  D.dist_arc F i (a := 1) (b := 4) (by norm_num) (by norm_num)

theorem dist_alpha_delta (F : FanTree Γ G) (i : Fin 5) : Γ.dist (D.alpha i) (D.delta i) = 2 :=
  D.dist_arc F i (a := 2) (b := 4) (by norm_num) (by norm_num)

theorem dist_start_beta (F : FanTree Γ G) (i : Fin 5) : Γ.dist α (D.beta i) = 1 :=
  D.dist_vert F i (m := 1) (by norm_num)

theorem dist_start_alpha (F : FanTree Γ G) (i : Fin 5) : Γ.dist α (D.alpha i) = 2 :=
  D.dist_vert F i (m := 2) (by norm_num)

theorem dist_start_xi (F : FanTree Γ G) (i : Fin 5) : Γ.dist α (D.xi i) = 3 :=
  D.dist_vert F i (m := 3) (by norm_num)

end D10Set

end CFSG.Quasithin.Fan86
