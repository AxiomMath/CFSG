module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XW
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XInv
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Ord

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

variable {L : ZLab Γ G} {α : V}

theorem fcomm_one_of_comm {a b : G} (h : a * b = b * a) : fcomm a b = 1 := by
  have h1 : b⁻¹ * a * b = a := by
    rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  calc fcomm a b = a⁻¹ * (b⁻¹ * a * b) := by unfold fcomm; group
    _ = 1 := by rw [h1, inv_mul_cancel]

theorem fixes_conj_partner (F : FanTree Γ G) (h71c : Fan71c F L) {D₀ : D10Set L α} {g w₀ : G}
    {η' : V} (hgP : ∀ m, m ≤ 4 → g • (D₀.P 0).vert m = (D₀.P 0).vert m) (hw : IsW1 D₀ w₀)
    (hY : D₀.IsYPair η') (hη : w₀ • ((D₀.x ^ 2)⁻¹ • η') = (D₀.x ^ 2)⁻¹ • η') :
    w₀ • ((D₀.x ^ 2)⁻¹ • g⁻¹ • η') = (D₀.x ^ 2)⁻¹ • g⁻¹ • η' := by
  have hT := F.isTree
  obtain ⟨-, -, -, -, h5, -⟩ := hY
  obtain ⟨m, hmη, hdm⟩ := IsTree.exists_adj_dist_succ hT (u := D₀.alpha 0) (v := η') (n := 1) h5
  have ham : Γ.Adj (D₀.alpha 0) m := dist_eq_one_iff_adj.1 hdm
  have hgm : g • m = m := by
    refine F.frobenius_two (D₀.alpha 0) ((D₀.P 0).vert 1) ((D₀.P 0).vert 3)
      ((D₀.P 0).adj 1 (by norm_num)).symm ((D₀.P 0).adj 2 (by norm_num))
      ((D₀.P 0).nb 1 (by norm_num)) g (MulAction.mem_stabilizer_iff.2 (hgP 2 (by norm_num)))
      (hgP 1 (by norm_num)) (hgP 3 (by norm_num)) m ham
  have hadj1 : Γ.Adj m (g⁻¹ • η') := by
    have := (F.adj_smul g⁻¹ m η').2 hmη
    rwa [inv_smul_eq_iff.2 hgm.symm] at this
  have hxA : (D₀.x ^ 2)⁻¹ • D₀.alpha 0 = D₀.alpha 2 :=
    D₀.x_pow_inv_smul_vert F h71c 2 0 (m := 2) (by norm_num)
  have hwA : w₀ • D₀.alpha 2 = D₀.alpha 2 := (Arc.mem_stab G).1 hw.fixes 2 (by norm_num)
  have hwm' : w₀ • ((D₀.x ^ 2)⁻¹ • m) = (D₀.x ^ 2)⁻¹ • m := by
    refine F.frobenius_two (D₀.alpha 2) ((D₀.P 2).vert 1) ((D₀.P 2).vert 3)
      ((D₀.P 2).adj 1 (by norm_num)).symm ((D₀.P 2).adj 2 (by norm_num))
      ((D₀.P 2).nb 1 (by norm_num)) w₀ (MulAction.mem_stabilizer_iff.2 hwA)
      ((Arc.mem_stab G).1 hw.fixes 1 (by norm_num)) ((Arc.mem_stab G).1 hw.fixes 3 (by norm_num))
      _ ?_
    rw [← hxA]
    exact (F.adj_smul _ _ _).2 ham
  have hAm' : Γ.Adj ((D₀.x ^ 2)⁻¹ • m) (D₀.alpha 2) := by
    rw [← hxA]
    exact (F.adj_smul _ _ _).2 ham.symm
  have hAζ : D₀.alpha 2 ≠ (D₀.x ^ 2)⁻¹ • η' := by
    rw [← hxA]
    intro h
    have h' := MulAction.injective _ h
    rw [← h', SimpleGraph.dist_self] at h5
    omega
  have hζm' : Γ.Adj ((D₀.x ^ 2)⁻¹ • m) ((D₀.x ^ 2)⁻¹ • η') := (F.adj_smul _ _ _).2 hmη
  have hζ''m' : Γ.Adj ((D₀.x ^ 2)⁻¹ • m) ((D₀.x ^ 2)⁻¹ • g⁻¹ • η') := (F.adj_smul _ _ _).2 hadj1
  exact F.frobenius_two ((D₀.x ^ 2)⁻¹ • m) (D₀.alpha 2) ((D₀.x ^ 2)⁻¹ • η') hAm' hζm' hAζ
    w₀ (MulAction.mem_stabilizer_iff.2 hwm') hwA hη _ hζ''m'

theorem commutes_of_compat (F : FanTree Γ G) (h71c : Fan71c F L) {D₀ D : D10Set L α}
    {g w₀ : G} {η' : V} (h : Compat D₀ D g)
    (hDP : ∀ m, m ≤ 4 → (D.P 0).vert m = (D₀.P 0).vert m) (hw : IsW1 D₀ w₀)
    (hY : D₀.IsYPair η') (hη : w₀ • ((D₀.x ^ 2)⁻¹ • η') = (D₀.x ^ 2)⁻¹ • η') :
    fcomm (g * w₀ * g⁻¹) (D.y η' 2) = 1 := by
  have hgP : ∀ m, m ≤ 4 → g • (D₀.P 0).vert m = (D₀.P 0).vert m := fun m hm => by
    rw [h.1 m hm, hDP m hm]
  have hX := h.x_eq F
  obtain ⟨-, hv2⟩ := valence_of_isZ2Pair F D₀.val hY
  have hζ := fixes_conj_partner F h71c hgP hw hY hη
  have hδ0 : g⁻¹ • D₀.delta 0 = D₀.delta 0 := inv_smul_eq_iff.2 (hgP 4 le_rfl).symm
  have hxs : (D₀.x ^ 2)⁻¹ • D₀.delta 0 = D₀.delta 2 :=
    D₀.x_pow_inv_smul_vert F h71c 2 0 (m := 4) (by norm_num)
  have hv2' : valence Γ (g⁻¹ • η') = 5 := by rw [valence_smul F]; exact hv2
  have hv2'' : valence Γ ((D₀.x ^ 2)⁻¹ • g⁻¹ • η') = 5 := by rw [valence_smul F]; exact hv2'
  have ha : g⁻¹ * L.z (D₀.delta 0) * g = L.z (D₀.delta 0) := by
    rw [← L.z_inv_smul g (D₀.valence_delta F 0), hδ0]
  have hb : g⁻¹ * L.z η' * g = L.z (g⁻¹ • η') := (L.z_inv_smul g hv2).symm
  have hc : (D₀.x ^ 2)⁻¹ * L.z (D₀.delta 0) * D₀.x ^ 2 = L.z (D₀.delta 2) := by
    rw [← L.z_inv_smul (D₀.x ^ 2) (D₀.valence_delta F 0), hxs]
  have hd : (D₀.x ^ 2)⁻¹ * L.z (g⁻¹ • η') * D₀.x ^ 2 = L.z ((D₀.x ^ 2)⁻¹ • g⁻¹ • η') :=
    (L.z_inv_smul (D₀.x ^ 2) hv2').symm
  have e1 : D.delta 0 = D₀.delta 0 := hDP 4 le_rfl
  have hy : D.y η' 2 = g * (L.z (D₀.delta 2) * L.z ((D₀.x ^ 2)⁻¹ • g⁻¹ • η')) * g⁻¹ := by
    show (D.x ^ 2)⁻¹ * (L.z (D.delta 0) * L.z η') * D.x ^ 2 = _
    rw [e1, hX, conj_pow]
    calc (g * D₀.x ^ 2 * g⁻¹)⁻¹ * (L.z (D₀.delta 0) * L.z η') * (g * D₀.x ^ 2 * g⁻¹)
        = g * ((D₀.x ^ 2)⁻¹ * ((g⁻¹ * L.z (D₀.delta 0) * g) * (g⁻¹ * L.z η' * g)) *
            D₀.x ^ 2) * g⁻¹ := by group
      _ = g * ((D₀.x ^ 2)⁻¹ * (L.z (D₀.delta 0) * L.z (g⁻¹ • η')) * D₀.x ^ 2) * g⁻¹ := by
          rw [ha, hb]
      _ = g * (((D₀.x ^ 2)⁻¹ * L.z (D₀.delta 0) * D₀.x ^ 2) *
            ((D₀.x ^ 2)⁻¹ * L.z (g⁻¹ • η') * D₀.x ^ 2)) * g⁻¹ := by group
      _ = _ := by rw [hc, hd]
  have hc1 : w₀ * L.z (D₀.delta 2) = L.z (D₀.delta 2) * w₀ :=
    (h71c.comm_z_iff (D₀.valence_delta F 2) w₀).2 ((Arc.mem_stab G).1 hw.fixes 4 (by norm_num))
  have hc2 : w₀ * L.z ((D₀.x ^ 2)⁻¹ • g⁻¹ • η') = L.z ((D₀.x ^ 2)⁻¹ • g⁻¹ • η') * w₀ :=
    (h71c.comm_z_iff hv2'' w₀).2 hζ
  have hcomm : w₀ * (L.z (D₀.delta 2) * L.z ((D₀.x ^ 2)⁻¹ • g⁻¹ • η')) =
      (L.z (D₀.delta 2) * L.z ((D₀.x ^ 2)⁻¹ • g⁻¹ • η')) * w₀ := by
    rw [← mul_assoc, hc1, mul_assoc, hc2, mul_assoc]
  rw [hy]
  apply fcomm_one_of_comm
  calc g * w₀ * g⁻¹ * (g * (L.z (D₀.delta 2) * L.z ((D₀.x ^ 2)⁻¹ • g⁻¹ • η')) * g⁻¹)
      = g * (w₀ * (L.z (D₀.delta 2) * L.z ((D₀.x ^ 2)⁻¹ • g⁻¹ • η'))) * g⁻¹ := by group
    _ = g * ((L.z (D₀.delta 2) * L.z ((D₀.x ^ 2)⁻¹ • g⁻¹ • η')) * w₀) * g⁻¹ := by rw [hcomm]
    _ = _ := by group

end P4X

end CFSG.Quasithin.Fan86
