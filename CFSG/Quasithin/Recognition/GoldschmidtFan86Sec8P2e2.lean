module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2e1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2d2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fin5_kstar_pair : ∀ i j : Fin 5, i ≠ j →
    midlab (kstar i j) (kstar j i) = midlab i j ∧ kstar (kstar i j) (kstar j i) = j ∧
      kstar (kstar j i) (kstar i j) = i := by
  unfold midlab kstar
  decide

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem u_xi_moved_left (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) :
    (D.y δ' i * D.y δ' j) • D.xi i ≠ D.xi i := fun hfix =>
  D.u_alpha_moved_left F h h81 hY hij (fixes_parent F (D.u_fixes_start F h h81 hY i j)
    (D.adj_alpha_xi i) (by rw [D.dist_start_alpha F, D.dist_start_xi F]) hfix)

theorem u_xi_moved_right (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) :
    (D.y δ' i * D.y δ' j) • D.xi j ≠ D.xi j := fun hfix =>
  D.u_alpha_moved_right F h h81 hY hij (fixes_parent F (D.u_fixes_start F h h81 hY i j)
    (D.adj_alpha_xi j) (by rw [D.dist_start_alpha F, D.dist_start_xi F]) hfix)

theorem g_xi_moved (F : FanTree Γ G) (h7 : Fan7 F L) (h512 : Fan512 F L) {i j : Fin 5}
    (hij : i ≠ j) {k : Fin 5} (hk : k = kstar i j ∨ k = kstar j i) :
    (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) • D.xi k ≠ D.xi k := by
  obtain ⟨⟨-, -, hi1, hi2, hi3, hj1, hj2, hj3, hij'⟩, -, -⟩ := fin5_midlab_facts i j hij
  obtain ⟨hm, hs1, hs2⟩ := fin5_kstar_pair i j hij
  intro hfix
  have := (D.fixed_iff F h7 h512 hij' k (n := 3) (by norm_num)).1 hfix
  rw [hm, hs1, hs2] at this
  rcases this with h1 | ⟨-, h2⟩ | ⟨h3, -⟩
  · rcases hk with rfl | rfl
    · exact hi3 h1
    · exact hj3 h1
  · omega
  · rcases hk with rfl | rfl
    · rcases h3 with h4 | h4
      · exact hi2 h4
      · exact hi1 h4
    · rcases h3 with h4 | h4
      · exact hj2 h4
      · exact hj1 h4

theorem u_xi_moved_star (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L) (h82 : Fan82a F L)
    (h512 : Fan512 F L) {δ' : V} (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) {k : Fin 5}
    (hk : k = kstar i j ∨ k = kstar j i) : (D.y δ' i * D.y δ' j) • D.xi k ≠ D.xi k := by
  intro hfix
  have h71c : Fan71c F L := h7.2.2.1
  have hv := fan_8_3d2 h7 h81 h82 h512 α D δ' hY i j hij
  have hvu : fcomm (D.y δ' i) (D.y δ' j) =
      (D.y δ' i * D.y δ' j) * (D.y δ' i * D.y δ' j) := by
    rw [D.fcomm_y_eq F h71c hY]
    group
  apply D.g_xi_moved F h7 h512 hij hk
  rw [← hv, hvu, mul_smul, hfix, hfix]

theorem u_delta_inv_eq (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L) (h82 : Fan82a F L)
    (h512 : Fan512 F L) {δ' : V} (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) :
    (D.y δ' i * D.y δ' j)⁻¹ • D.delta (midlab i j) =
      L.z (D.alpha (kstar i j)) • D.delta (midlab i j) := by
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨⟨-, -, -, -, -, -, -, -, -⟩, ⟨hmid, hmid2⟩, -⟩ := fin5_midlab_facts i j hij
  obtain ⟨hk1, hk2⟩ := fin5_kstar_mid i j hij
  have hzm2 := L.z_mul_self (D.valence_delta F (midlab i j))
  have hyi := D.y_mul_self' F h71c hY i
  have hyj := D.y_mul_self' F h71c hY j
  have hyi' : (D.y δ' i)⁻¹ = D.y δ' i := inv_eq_of_mul_eq_one_right hyi
  have hyj' : (D.y δ' j)⁻¹ = D.y δ' j := inv_eq_of_mul_eq_one_right hyj
  have hr1 : L.z (D.delta (midlab i j)) * D.y δ' i * L.z (D.delta (midlab i j)) = D.y δ' j := by
    rw [D.y_refl F h71c hY (midlab i j) i, hmid]
  have hr2 : L.z (D.delta (midlab i j)) * D.y δ' j * L.z (D.delta (midlab i j)) = D.y δ' i := by
    rw [D.y_refl F h71c hY (midlab i j) j, hmid2]
  have hu : L.z (D.delta (midlab i j)) * (D.y δ' i * D.y δ' j) * L.z (D.delta (midlab i j)) =
      (D.y δ' i * D.y δ' j)⁻¹ := by
    have e : (L.z (D.delta (midlab i j)) * D.y δ' i * L.z (D.delta (midlab i j))) *
        (L.z (D.delta (midlab i j)) * D.y δ' j * L.z (D.delta (midlab i j))) =
        L.z (D.delta (midlab i j)) * (D.y δ' i * D.y δ' j) * L.z (D.delta (midlab i j)) := by
      calc _ = L.z (D.delta (midlab i j)) * D.y δ' i * (L.z (D.delta (midlab i j)) *
            L.z (D.delta (midlab i j))) * D.y δ' j * L.z (D.delta (midlab i j)) := by group
        _ = _ := by rw [hzm2]; group
    rw [← e, hr1, hr2, mul_inv_rev, hyi', hyj']
  have hvu : fcomm (D.y δ' i) (D.y δ' j) = (D.y δ' i * D.y δ' j) * (D.y δ' i * D.y δ' j) := by
    rw [D.fcomm_y_eq F h71c hY]
    group
  have hvδ : valence Γ (D.delta (midlab i j)) = 5 := D.valence_delta F _
  have hvinv : L.z ((D.y δ' i * D.y δ' j)⁻¹ • D.delta (midlab i j)) * L.z (D.delta (midlab i j)) =
      (fcomm (D.y δ' i) (D.y δ' j))⁻¹ := by
    rw [L.z_inv_smul _ hvδ, hvu, mul_inv_rev, ← mul_inv_rev]
    calc (D.y δ' i * D.y δ' j)⁻¹ * L.z (D.delta (midlab i j)) * (D.y δ' i * D.y δ' j) *
          L.z (D.delta (midlab i j))
        = (D.y δ' i * D.y δ' j)⁻¹ * (L.z (D.delta (midlab i j)) * (D.y δ' i * D.y δ' j) *
          L.z (D.delta (midlab i j))) := by group
      _ = (D.y δ' i * D.y δ' j)⁻¹ * (D.y δ' i * D.y δ' j)⁻¹ := by rw [hu]
      _ = _ := by rw [← mul_inv_rev]
  have hv := fan_8_3d2 h7 h81 h82 h512 α D δ' hY i j hij
  have hcommzz : ∀ s t : Fin 5,
      L.z (D.alpha s) * L.z (D.alpha t) = L.z (D.alpha t) * L.z (D.alpha s) := by
    intro s t
    by_cases hst : s = t
    · rw [hst]
    · exact h71c.z_comm_of_dist_le (D.valence_alpha F s) (D.valence_alpha F t)
        (by rw [D.dist_alpha_alpha F h71c hst])
  have hzs : ∀ s : Fin 5, L.z (D.alpha s) * L.z (D.alpha s) = 1 :=
    fun s => L.z_mul_self (D.valence_alpha F s)
  have hgg : (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) *
      (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) = 1 := by
    calc _ = L.z (D.alpha (kstar i j)) * (L.z (D.alpha (kstar j i)) *
          L.z (D.alpha (kstar i j))) * L.z (D.alpha (kstar j i)) := by group
      _ = L.z (D.alpha (kstar i j)) * (L.z (D.alpha (kstar i j)) *
          L.z (D.alpha (kstar j i))) * L.z (D.alpha (kstar j i)) := by
        rw [hcommzz (kstar j i) (kstar i j)]
      _ = (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar i j))) *
          (L.z (D.alpha (kstar j i)) * L.z (D.alpha (kstar j i))) := by group
      _ = 1 := by rw [hzs, hzs, one_mul]
  have h1 : L.z ((D.y δ' i * D.y δ' j)⁻¹ • D.delta (midlab i j)) * L.z (D.delta (midlab i j)) =
      L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)) := by
    rw [hvinv, hv]
    exact inv_eq_of_mul_eq_one_right hgg
  have hgd := D.z_pair_eq_conj F h71c (a := kstar i j) (b := kstar j i) (m := midlab i j) hk1
  have h2 := mul_right_cancel (h1.trans hgd)
  refine h71c.z_injective ?_ ?_ h2
  · rw [valence_smul F]
    exact hvδ
  · rw [valence_smul F]
    exact hvδ

theorem u_xi_moved_mid (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L) (h82 : Fan82a F L)
    (h512 : Fan512 F L) {δ' : V} (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) :
    (D.y δ' i * D.y δ' j) • D.xi (midlab i j) ≠ D.xi (midlab i j) := by
  intro hfix
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨⟨-, -, -, -, hi3, -, -, -, -⟩, -, -⟩ := fin5_midlab_facts i j hij
  have hdel := D.u_delta_inv_eq F h7 h81 h82 h512 hY hij
  have hxi' : (D.y δ' i * D.y δ' j)⁻¹ • D.xi (midlab i j) = D.xi (midlab i j) :=
    inv_smul_eq_iff.2 hfix.symm
  have hA1 : Γ.Adj (D.xi (midlab i j)) (L.z (D.alpha (kstar i j)) • D.delta (midlab i j)) := by
    have := (F.adj_smul (D.y δ' i * D.y δ' j)⁻¹ (D.xi (midlab i j)) (D.delta (midlab i j))).2
      (D.adj_xi_delta _)
    rwa [hxi', hdel] at this
  have hA2 := (F.adj_smul (L.z (D.alpha (kstar i j))) (D.xi (midlab i j))
    (D.delta (midlab i j))).2 (D.adj_xi_delta _)
  have hzα : L.z (D.alpha (kstar i j)) • α = α :=
    (h71c.z_smul_eq_iff (D.valence_alpha F _) α).2 (by rw [D.dist_alpha_start F]; norm_num)
  have hd4 : Γ.dist α (L.z (D.alpha (kstar i j)) • D.delta (midlab i j)) = 4 := by
    have := dist_smul F (L.z (D.alpha (kstar i j))) α (D.delta (midlab i j))
    rw [hzα, D.dist_delta F] at this
    exact this
  have hd3 : Γ.dist α (L.z (D.alpha (kstar i j)) • D.xi (midlab i j)) = 3 := by
    have := dist_smul F (L.z (D.alpha (kstar i j))) α (D.xi (midlab i j))
    rw [hzα, D.dist_start_xi F] at this
    exact this
  have heq := IsTree.eq_of_dist_succ F.isTree (r := α) hA1 hA2
    (by rw [D.dist_start_xi F, hd4]) (by rw [hd3, hd4])
  have hmv : L.z (D.alpha (kstar i j)) • D.xi (midlab i j) ≠ D.xi (midlab i j) := fun e => by
    have h5 := (h71c.z_smul_eq_iff (D.valence_alpha F _) _).1 e
    have h6 := D.dist_vert_ne F h71c hi3 (m := 2) (m' := 3) (by norm_num) (by norm_num)
    have h7' : Γ.dist (D.alpha (kstar i j)) (D.xi (midlab i j)) = 2 + 3 := h6
    omega
  exact hmv heq.symm

theorem u_xi_moved (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L) (h82 : Fan82a F L)
    (h512 : Fan512 F L) {δ' : V} (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) (k : Fin 5) :
    (D.y δ' i * D.y δ' j) • D.xi k ≠ D.xi k := by
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨-, -, hall⟩ := fin5_midlab_facts i j hij
  rcases hall k with h | h | h | h | h
  · rw [h]
    exact D.u_xi_moved_mid F h7 h81 h82 h512 hY hij
  · rw [h]
    exact D.u_xi_moved_left F h71c h81 hY hij
  · rw [h]
    exact D.u_xi_moved_right F h71c h81 hY hij
  · exact D.u_xi_moved_star F h7 h81 h82 h512 hY hij (Or.inl h)
  · exact D.u_xi_moved_star F h7 h81 h82 h512 hY hij (Or.inr h)

theorem u_delta_moved (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L) (h82 : Fan82a F L)
    (h512 : Fan512 F L) {δ' : V} (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) (k : Fin 5) :
    (D.y δ' i * D.y δ' j) • D.delta k ≠ D.delta k := fun hfix =>
  D.u_xi_moved F h7 h81 h82 h512 hY hij k (fixes_parent F (D.u_fixes_start F h7.2.2.1 h81 hY i j)
    (D.adj_xi_delta k) (by rw [D.dist_start_xi F, D.dist_delta F]) hfix)

end D10Set

end CFSG.Quasithin.Fan86
