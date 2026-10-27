module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87C
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Alg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt2

public section

namespace CFSG.Quasithin.Fan86.F87

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V}

theorem valence_ypair (F : FanTree Γ G) (D : D10Set L α) {δ' : V} (hY : D.IsYPair δ') :
    valence Γ δ' = 5 :=
  valence_of_dist_even F D.val (by rw [hY.2.2.2.2.2.2.1])

theorem y_sq (h7 : Fan7 F L) (D : D10Set L α) {δ' : V} (hY : D.IsYPair δ') (k : Fin 5) :
    D.y δ' k * D.y δ' k = 1 := by
  have h71c : Fan71c F L := h7.2.2.1
  have hv := valence_ypair F D hY
  have hZ := D.isZ2Pair_translate F h71c hY k
  have ha : valence Γ (D.delta k) = 5 := D.valence_delta F k
  have hb : valence Γ ((D.x ^ k.val)⁻¹ • δ') = 5 := by rw [valence_smul F]; exact hv
  have hd : Γ.dist (D.delta k) ((D.x ^ k.val)⁻¹ • δ') ≤ 4 := by
    have := F.isTree.connected.dist_triangle (u := D.delta k) (v := D.alpha k)
      (w := (D.x ^ k.val)⁻¹ • δ')
    have h1 := hZ.2.2.2.1
    have h2 := hZ.2.2.2.2.1
    rw [SimpleGraph.dist_comm] at h1
    omega
  have hc := h71c.z_comm_of_dist_le ha hb hd
  rw [D.y_eq F h71c hv k]
  calc L.z (D.delta k) * L.z ((D.x ^ k.val)⁻¹ • δ') *
        (L.z (D.delta k) * L.z ((D.x ^ k.val)⁻¹ • δ'))
      = L.z (D.delta k) * (L.z ((D.x ^ k.val)⁻¹ • δ') * L.z (D.delta k)) *
          L.z ((D.x ^ k.val)⁻¹ • δ') := by group
    _ = L.z (D.delta k) * (L.z (D.delta k) * L.z ((D.x ^ k.val)⁻¹ • δ')) *
          L.z ((D.x ^ k.val)⁻¹ • δ') := by rw [hc]
    _ = (L.z (D.delta k) * L.z (D.delta k)) *
          (L.z ((D.x ^ k.val)⁻¹ • δ') * L.z ((D.x ^ k.val)⁻¹ • δ')) := by group
    _ = 1 := by rw [L.z_mul_self ha, L.z_mul_self hb, one_mul]

theorem yy_sq (h7 : Fan7 F L) (h83d : Fan83d F L) (D : D10Set L α) {δ' : V} (hY : D.IsYPair δ')
    {k l : Fin 5} (hkl : k ≠ l) :
    D.y δ' k * D.y δ' l * (D.y δ' k * D.y δ' l) =
      L.z (D.alpha (kstar k l)) * L.z (D.alpha (kstar l k)) := by
  have hk := y_sq h7 D hY k
  have hl := y_sq h7 D hY l
  rw [← h83d.2 α D δ' hY k l hkl]
  unfold fcomm
  rw [inv_eq_of_mul_eq_one_right hk, inv_eq_of_mul_eq_one_right hl]
  group

theorem mem_zpowers_involution {z x : G} (hz : z * z = 1) (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, hz2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]

theorem fcomm_y_c (h7 : Fan7 F L) (h83 : Fan83 F L) (h84 : Fan84a F L) (D : D10Set L α)
    {δ' : V} (hY : D.IsYPair δ') {c : G} (hc : c ∈ D.calpha) (h4 : orderOf c = 4) (k : Fin 5) :
    fcomm (D.y δ' k) c = L.z (D.alpha k) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hv := valence_ypair F D hY
  have hzk := L.z_mul_self (D.valence_alpha F k)
  have hne : D.calpha ≠ Subgroup.zpowers (L.z α) := by
    intro h
    rw [h] at hc
    have : c * c = 1 := by
      rcases mem_zpowers_involution (L.z_mul_self D.val) hc with h1 | h1
      · rw [h1, one_mul]
      · rw [h1]
        exact L.z_mul_self D.val
    have h2 := orderOf_dvd_of_pow_eq_one (show c ^ 2 = 1 by rw [pow_two]; exact this)
    rw [h4] at h2
    omega
  have hZ := h83.2.2.1 α D hne k _ _ (D.isZ2Pair_translate F h71c hY k)
  rw [← D.y_eq F h71c hv k] at hZ
  have hmem : fcomm (D.y δ' k) c ∈ Subgroup.zpowers (L.z (D.alpha k)) := by
    rw [← hZ]
    exact Subgroup.subset_closure ⟨c, hc, rfl⟩
  rcases mem_zpowers_involution hzk hmem with h1 | h1
  · exfalso
    have hcomm : ∀ c' ∈ D.calpha, fcomm (D.y δ' k) c' = 1 := by
      intro c' hc'
      rw [calpha_eq_zpowers h84 D hc h4] at hc'
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
      have hcm : Commute (D.y δ' k) c := fcomm_eq_one_iff.1 h1
      exact fcomm_eq_one_iff.2 (hcm.zpow_right n).eq
    have hbot : Subgroup.closure {g | ∃ c' ∈ D.calpha, g = fcomm (D.y δ' k) c'} = ⊥ := by
      rw [eq_bot_iff, Subgroup.closure_le]
      rintro g ⟨c', hc', rfl⟩
      rw [hcomm c' hc']
      exact Subgroup.one_mem _
    rw [hbot] at hZ
    have : L.z (D.alpha k) ∈ Subgroup.zpowers (L.z (D.alpha k)) := Subgroup.mem_zpowers _
    rw [← hZ] at this
    exact L.z_ne_one (D.valence_alpha F k) (Subgroup.mem_bot.1 this)
  · exact h1

theorem fcomm_c_yy (h7 : Fan7 F L) (h83 : Fan83 F L) (h84 : Fan84a F L) (D : D10Set L α)
    {δ' : V} (hY : D.IsYPair δ') {c : G} (hc : c ∈ D.calpha) (h4 : orderOf c = 4) {k l : Fin 5}
    (hkl : k ≠ l) :
    fcomm c (D.y δ' k * D.y δ' l) = L.z (D.alpha l) * (L.z (D.alpha k) * L.z α) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hα : valence Γ α = 5 := D.val
  have hzk := L.z_inv (D.valence_alpha F k)
  have hzl := L.z_inv (D.valence_alpha F l)
  have e1 : fcomm c (D.y δ' k) = L.z (D.alpha k) := by
    rw [← fcomm_inv_eq, fcomm_y_c h7 h83 h84 D hY hc h4 k, hzk]
  have e2 : fcomm c (D.y δ' l) = L.z (D.alpha l) := by
    rw [← fcomm_inv_eq, fcomm_y_c h7 h83 h84 D hY hc h4 l, hzl]
  have hb : fcomm (D.y δ' l) (L.z (D.alpha k)) = L.z α := by
    simpa [hkl.symm] using h83.2.1 α D δ' hY l k
  have hzs : L.z (D.alpha k) ∈ MulAction.stabilizer G α :=
    (h71c.z_mem_stabilizer_iff (D.valence_alpha F k) α).2 (by
      rw [SimpleGraph.dist_comm, D.dist_start_alpha F k]
      norm_num)
  have hcomm := L.comm_z_of_mem_stabilizer hα hzs
  have hconj : (D.y δ' l)⁻¹ * L.z (D.alpha k) * D.y δ' l = L.z (D.alpha k) * L.z α := by
    unfold fcomm at hb
    rw [hzk] at hb
    calc (D.y δ' l)⁻¹ * L.z (D.alpha k) * D.y δ' l
        = ((D.y δ' l)⁻¹ * L.z (D.alpha k) * D.y δ' l * L.z (D.alpha k)) *
          (L.z (D.alpha k))⁻¹ := by group
      _ = L.z α * L.z (D.alpha k) := by rw [hb, hzk]
      _ = L.z (D.alpha k) * L.z α := hcomm.symm
  rw [fcomm_mul_right, e1, e2, hconj]

end CFSG.Quasithin.Fan86.F87
