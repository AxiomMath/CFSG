module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Pres4b
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Pres3b

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_9_15 {F : FanTree Γ G} {L : ZLab Γ G} (H : P5Hyp F L) : Fan915 F L := by
  intro S hS
  obtain ⟨e, he, hid⟩ := S.exists_ids H hS
  have hGE := F.card_stabilizer_eq_five_mul S.D.val S.adj_alpha_beta
  rcases S.D.card_stabilizer_cases F H.h7 H.h8 H.h65 H.h512 with ⟨h2, hcard⟩ | ⟨h4, hcard⟩
  · refine ⟨fun _ => Or.inl ⟨rfl, admitsPres11_of_data (S.presData11 H hS hcard h2 he hid)⟩,
      fun hE => ?_⟩
    rw [hGE, hE] at hcard
    omega
  · refine ⟨fun hE => ?_, fun _ => ?_⟩
    · rw [hGE, hE] at hcard
      omega
    · obtain ⟨d₁, d₂, hcA⟩ := (H.h99 S h4).1 (S.star_sq H hS)
      obtain ⟨-, -, -, a4, -, a6, -, -, -, -⟩ := H.h95.2.2.2 S
      have hcx : S.xβ⁻¹ * S.c * S.xβ = S.yEta 1 * S.yEta 3 * S.zMu1 3 * S.zMu1 4 * S.c *
          S.zMu1 2 ^ (d₁ : ℕ) * L.z S.α ^ (d₂ : ℕ) := by
        rw [← S.cA_one, hcA, a4, a6]
      obtain ⟨hza1, hz21, hz2za⟩ := S.z_ne H
      have hR := S.p1Rel H
      obtain ⟨hd2, -⟩ := hid.p2cRel913 hR (S.p1cRel H h4) (S.fcomm_wc H h4) (by omega)
        (by omega) hcx hza1 hz21 hz2za
      rw [hd2] at hcx
      exact Or.inr ⟨rfl, admitsPres12_of_data (S.presData12 H hcard h4 he (d := (d₁ : ℕ))
        (by omega) hid hcx)⟩

end CFSG.Quasithin.Fan86
