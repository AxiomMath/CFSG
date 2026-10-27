module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Rel

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem zGroup_two_le (F : FanTree Γ G) (h : Fan71c F L) (h512 : Fan512 F L) {T : Subgroup G}
    (hz : ∀ j, L.z (D.alpha j) ∈ T) (hza : L.z α ∈ T) : L.zGroup 2 α ≤ T := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨l, hl, hl5, rfl⟩
  have hd : Γ.dist α l = 0 ∨ Γ.dist α l = 1 ∨ Γ.dist α l = 2 := by omega
  rcases hd with hd | hd | hd
  · have : α = l := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 hd).resolve_right
      (fun hr => hr (F.isTree.connected.preconnected α l))
    rw [← this]
    exact hza
  · exact absurd (valence_of_dist_odd F D.val (by rw [hd])) (by omega)
  · obtain ⟨b, hbl, hb⟩ := IsTree.exists_adj_dist_succ F.isTree (u := α) (v := l) (n := 1) hd
    have hαb : Γ.Adj α b := dist_eq_one_iff_adj.1 hb
    obtain ⟨i, rfl⟩ := D.exists_beta_eq F h hαb
    obtain ⟨t, hts, hat, hjt⟩ := exists_third_neighbor (D.valence_beta F i)
      (D.adj_start_beta i).symm (D.adj_beta_alpha i) (D.alpha_ne_start i).symm
    have hmem : l ∈ Γ.neighborSet (D.beta i) := hbl
    rw [hts] at hmem
    have hne : l ≠ α := fun e => by
      rw [e, SimpleGraph.dist_self] at hd
      omega
    rcases hmem with h1 | h1 | h1
    · exact absurd h1 hne
    · rw [h1]
      exact hz i
    · have h3 := h512.2.2.1 (D.beta i) α (D.alpha i) t (D.valence_beta F i) hts
        (D.alpha_ne_start i).symm hat hjt
      have hzt : L.z t = L.z (D.alpha i) * L.z α := by
        rw [eq_inv_of_mul_eq_one_right h3, mul_inv_rev, L.z_inv (D.valence_alpha F i),
          L.z_inv D.val]
      rw [h1, hzt]
      exact mul_mem (hz i) hza

end D10Set

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

@[expose] def w1 : G := S.D.x ^ 2 * S.w * (S.D.x ^ 2)⁻¹

theorem w_sq_ne_one (F : FanTree Γ G) (h : Fan71c F L) : S.w * S.w ≠ 1 := by
  rcases S.isW1.sq with hq | hq
  · rw [hq]
    intro h1
    have h2 : L.z (S.D.delta 2) = L.z S.α := by
      calc L.z (S.D.delta 2) = (L.z S.α)⁻¹ := eq_inv_of_mul_eq_one_left h1
        _ = L.z S.α := L.z_inv S.D.val
    have h3 := h.z_injective (S.D.valence_delta F 2) S.D.val h2
    have hd := S.D.dist_delta F 2
    rw [h3, SimpleGraph.dist_self] at hd
    omega
  · rw [hq]
    exact L.z_ne_one (S.D.valence_delta F 2)

theorem orderOf_w (F : FanTree Γ G) (h : Fan71c F L) : orderOf S.w = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf S.w = 2 ^ (1 + 1) := orderOf_eq_prime_pow (p := 2) (n := 1)
    (by rw [pow_one, pow_two]; exact S.w_sq_ne_one F h) (S.w_pow_four F h)
  rw [h1]
  norm_num

theorem w1_mem_stab (F : FanTree Γ G) (h : Fan71c F L) : S.w1 ∈ (S.D.P 0).stab G := by
  refine (Arc.mem_stab G).2 fun m hm => ?_
  have e : (S.D.x ^ 2)⁻¹ • (S.D.P 0).vert m = (S.D.P 2).vert m := by
    have := S.D.x_pow_inv_smul_vert F h 2 0 hm
    exact this.trans (by congr 1)
  have hv : (S.D.P 0).vert m = S.D.x ^ 2 • (S.D.P 2).vert m := by
    rw [← e, smul_inv_smul]
  show (S.D.x ^ 2 * S.w * (S.D.x ^ 2)⁻¹) • (S.D.P 0).vert m = (S.D.P 0).vert m
  rw [mul_smul, mul_smul, e, S.w_fix_vert m hm, ← hv]

theorem w1_conj : S.w1⁻¹ * S.D.x * S.w1 = S.D.x ^ 2 := by
  unfold w1
  calc (S.D.x ^ 2 * S.w * (S.D.x ^ 2)⁻¹)⁻¹ * S.D.x * (S.D.x ^ 2 * S.w * (S.D.x ^ 2)⁻¹)
      = S.D.x ^ 2 * (S.w⁻¹ * S.D.x * S.w) * (S.D.x ^ 2)⁻¹ := by group
    _ = S.D.x ^ 2 := by rw [S.x_w]; group

theorem w1_sq (F : FanTree Γ G) (h : Fan71c F L) :
    S.w1 * S.w1 = L.z (S.D.delta 0) ∨ S.w1 * S.w1 = L.z (S.D.delta 0) * L.z S.α := by
  have hw1w1 : S.w1 * S.w1 = S.D.x ^ 2 * (S.w * S.w) * (S.D.x ^ 2)⁻¹ := by
    unfold w1
    group
  have hz2 : S.D.x ^ 2 * L.z (S.D.delta 2) * (S.D.x ^ 2)⁻¹ = L.z (S.D.delta 0) := by
    rw [← L.equivariant (S.D.x ^ 2) (S.D.delta 2) (S.D.valence_delta F 2)]
    congr 1
    have := S.D.x_pow_inv_smul_vert F h 2 0 (m := 4) (by norm_num)
    have h4 : (S.D.x ^ 2)⁻¹ • S.D.delta 0 = S.D.delta 2 := this.trans (by congr 1)
    exact (inv_smul_eq_iff.1 h4).symm
  have hza : S.D.x ^ 2 * L.z S.α * (S.D.x ^ 2)⁻¹ = L.z S.α := by
    have hc := L.comm_z_of_mem_stabilizer S.D.val (pow_mem (S.D.x_mem_stabilizer F h) 2)
    calc S.D.x ^ 2 * L.z S.α * (S.D.x ^ 2)⁻¹ = (L.z S.α * S.D.x ^ 2) * (S.D.x ^ 2)⁻¹ := by
          rw [hc]
      _ = L.z S.α := by group
  rcases S.isW1.sq with hq | hq
  · right
    rw [hw1w1, hq]
    calc S.D.x ^ 2 * (L.z (S.D.delta 2) * L.z S.α) * (S.D.x ^ 2)⁻¹
        = (S.D.x ^ 2 * L.z (S.D.delta 2) * (S.D.x ^ 2)⁻¹) * (S.D.x ^ 2 * L.z S.α *
          (S.D.x ^ 2)⁻¹) := by group
      _ = L.z (S.D.delta 0) * L.z S.α := by rw [hz2, hza]
  · left
    rw [hw1w1, hq, hz2]

theorem isW1Elem_w1 (F : FanTree Γ G) (h : Fan71c F L) : IsW1Elem S.D S.w1 := by
  refine ⟨S.w1_mem_stab F h, ?_, S.w1_conj, S.w1_sq F h⟩
  have := (MulAut.conj (S.D.x ^ 2)).orderOf_eq S.w
  rw [MulAut.conj_apply] at this
  show orderOf (S.D.x ^ 2 * S.w * (S.D.x ^ 2)⁻¹) = 4
  rw [this]
  exact S.orderOf_w F h

theorem stabilizer_le (F : FanTree Γ G) (h : Fan71c F L) (h512 : Fan512 F L)
    (h83a : Fan83a F L) (h86c : Fan86c F L) {T : Subgroup G} (hx : S.D.x ∈ T) (hw : S.w ∈ T)
    (hza : L.z S.α ∈ T) (hy : ∀ j, S.yEta j ∈ T) (hz : ∀ j, S.zMu1 j ∈ T)
    (hC : S.D.calpha ≤ T) : MulAction.stabilizer G S.α ≤ T := by
  have hN : nbrStab Γ G S.α ≤ T := by
    rw [h83a S.α S.D S.η' S.isBeta.pair]
    refine sup_le ((Subgroup.closure_le _).2 ?_) (sup_le (S.D.zGroup_two_le F h h512 hz hza) hC)
    rintro g ⟨j, rfl⟩
    exact hy j
  rw [(h86c S.α S.D S.w1 (S.isW1Elem_w1 F h)).1]
  refine sup_le ((Subgroup.closure_le _).2 ?_) hN
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact hx
  · exact mul_mem (mul_mem (pow_mem hx 2) hw) (inv_mem (pow_mem hx 2))

end Sec9Cfg

end CFSG.Quasithin.Fan86
