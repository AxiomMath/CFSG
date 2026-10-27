module

public import CFSG.Quasithin.Recognition.M12AscFinal
public import CFSG.Quasithin.Recognition.M12AscD15
public import CFSG.Quasithin.Recognition.M12AscE4
public import CFSG.Quasithin.Recognition.M12AscY3

public section

namespace CFSG.Quasithin

open CFSG.GH74.M12 (Asc03Hyp q8Subgroups S_Asc03_simple S_M12_core)

theorem asc03b_m10Amalgam
    : Asc03b_M10Amalgam := by
  intro G _ _ hsimple z hyp hq8 h95
  have _ := hsimple
  obtain ⟨m⟩ := exists_ascModel_of_asc03_normal_q8 hyp hq8
  have h27 : 27 ∣ Nat.card G := by rw [h95]; norm_num
  obtain ⟨c⟩ := m.exists_cox hyp h27
  obtain ⟨y, hy1, hy2⟩ := AscModel.exists_outer hyp c
  have h : OuterData c y := ⟨hy1, hy2⟩
  obtain ⟨v, r, hv2, hvK, hvL, hrL, hrK, hr2, hrv, hvz⟩ := c.exists_vr hyp h27 h
  exact ⟨h.L, h.K, v, z, r,
    { KL := h.K_le_L
      L_card := h.L_card
      pts := h.pts
      L3 := h.L3
      Q8 := h.Q8
      v_sq := hv2
      v_K := hvK
      v_L := hvL
      r_L := hrL
      r_K := hrK
      r_sq := hr2
      rv := hrv
      z_sq := c.z_sq
      z_L := fun l hl => h.z_normalizes_L hl
      z_n := h.z_notin_L
      vz := hvz }⟩

theorem s_Asc03_simple
    : S_Asc03_simple :=
  S_Asc03_simple_of_M10Amalgam asc03b_m10Amalgam

end CFSG.Quasithin
