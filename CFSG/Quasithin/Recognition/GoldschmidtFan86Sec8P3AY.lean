module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3AZ
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Dist

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P3

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem z_alpha_mem_zGroup (F : FanTree Γ G) (k : Fin 5) : L.z (D.alpha k) ∈ L.zGroup 2 α :=
  Subgroup.subset_closure ⟨D.alpha k, (D.dist_start_alpha F k).le, D.valence_alpha F k, rfl⟩

theorem z_mem_zGroup (hα : valence Γ α = 5) : L.z α ∈ L.zGroup 2 α :=
  Subgroup.subset_closure ⟨α, by simp, hα, rfl⟩

theorem valence_of_isYPair (F : FanTree Γ G) {δ' : V} (hY : D.IsYPair δ') : valence Γ δ' = 5 :=
  valence_of_dist_even F D.val (by simp [hY.2.2.2.2.2.2.1])

theorem y_mul_self (F : FanTree Γ G) (h71c : Fan71c F L) {δ' : V} (hY : D.IsYPair δ')
    (i : Fin 5) : D.y δ' i * D.y δ' i = 1 := by
  have hv' := valence_of_isYPair D F hY
  obtain ⟨-, -, -, h4, h5, -⟩ := D.isZ2Pair_translate F h71c hY i
  have hv'' : valence Γ ((D.x ^ i.val)⁻¹ • δ') = 5 := by
    rw [valence_smul F]
    exact hv'
  have hdist : Γ.dist (D.delta i) ((D.x ^ i.val)⁻¹ • δ') ≤ 4 := by
    have h1 := F.isTree.connected.dist_triangle (u := D.delta i) (v := D.alpha i)
      (w := (D.x ^ i.val)⁻¹ • δ')
    have h2 : Γ.dist (D.delta i) (D.alpha i) = Γ.dist (D.alpha i) (D.delta i) :=
      SimpleGraph.dist_comm
    omega
  have hc := h71c.z_comm_of_dist_le (D.valence_delta F i) hv'' hdist
  have ha := L.z_mul_self (D.valence_delta F i)
  have hb := L.z_mul_self hv''
  rw [D.y_eq F h71c hv' i]
  calc (L.z (D.delta i) * L.z ((D.x ^ i.val)⁻¹ • δ')) *
        (L.z (D.delta i) * L.z ((D.x ^ i.val)⁻¹ • δ'))
      = (L.z (D.delta i) * L.z ((D.x ^ i.val)⁻¹ • δ')) *
        (L.z ((D.x ^ i.val)⁻¹ • δ') * L.z (D.delta i)) := by rw [← hc]
    _ = L.z (D.delta i) * (L.z ((D.x ^ i.val)⁻¹ • δ') * L.z ((D.x ^ i.val)⁻¹ • δ')) *
        L.z (D.delta i) := by group
    _ = 1 := by rw [hb, mul_one, ha]

theorem y_mem_nbrStab (h83a : Fan83a F L) {δ' : V} (hY : D.IsYPair δ') (i : Fin 5) :
    D.y δ' i ∈ nbrStab Γ G α := by
  rw [h83a α D δ' hY]
  exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, rfl⟩)

theorem fcomm_y_y_mem (F : FanTree Γ G) (h83d : Fan83d F L) {δ' : V} (hY : D.IsYPair δ')
    (i j : Fin 5) : fcomm (D.y δ' i) (D.y δ' j) ∈ L.zGroup 2 α := by
  by_cases hij : i = j
  · subst hij
    have : fcomm (D.y δ' i) (D.y δ' i) = 1 := by
      unfold fcomm
      group
    rw [this]
    exact one_mem _
  · rw [h83d.2 α D δ' hY i j hij]
    exact mul_mem (z_alpha_mem_zGroup D F _) (z_alpha_mem_zGroup D F _)

theorem fcomm_y_calpha_mem (F : FanTree Γ G) (h71c : Fan71c F L) (h83c : Fan83c F L) {δ' : V}
    (hY : D.IsYPair δ') (i : Fin 5) (hy : D.y δ' i ∈ MulAction.stabilizer G α) {c : G}
    (hc : c ∈ D.calpha) : fcomm (D.y δ' i) c ∈ L.zGroup 2 α := by
  by_cases hC : D.calpha = Subgroup.zpowers (L.z α)
  · rw [hC] at hc
    exact fcomm_mem_of_right_mem F hy ((Subgroup.zpowers_le.2 (z_mem_zGroup D.val)) hc)
  · have hv' := valence_of_isYPair D F hY
    have h1 := h83c α D hC i _ _ (D.isZ2Pair_translate F h71c hY i)
    have h2 : fcomm (L.z (D.delta i) * L.z ((D.x ^ i.val)⁻¹ • δ')) c ∈
        Subgroup.zpowers (L.z (D.alpha i)) := by
      rw [← h1]
      exact Subgroup.subset_closure ⟨c, hc, rfl⟩
    rw [D.y_eq F h71c hv' i]
    exact (Subgroup.zpowers_le.2 (z_alpha_mem_zGroup D F i)) h2

end Sec8P3

end CFSG.Quasithin.Fan86
