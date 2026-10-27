module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2Eps
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2C1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2V3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_3d2 {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h82 : Fan82a F L) (h512 : Fan512 F L) :
    ∀ (α : V) (D : D10Set L α) (δ' : V), D.IsYPair δ' → ∀ i j : Fin 5, i ≠ j →
      fcomm (D.y δ' i) (D.y δ' j) =
        L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)) := by
  intro α D δ' hY i j hij
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨c, hc, hvc⟩ := D.fcomm_y_mem_mul_calpha F h7 h81 h82 h512 hY hij
  obtain ⟨⟨-, -, hi1, -, -, hj1, -, -, -⟩, -, -⟩ := fin5_midlab_facts i j hij
  have hcfix : ∀ w, Γ.dist (D.beta i) w ≤ 2 → c • w = w := by
    intro w hw
    have h1 := D.fcomm_y_fixes_ball_left F h71c h81 hY i j w hw
    have h2 := D.fix_ball_two F h71c (a := kstar i j) (b := kstar j i) (k := i) hi1 hj1 hw
    rw [hvc, mul_smul] at h1
    exact MulAction.injective (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)))
      (h1.trans h2.symm)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (D.calpha_mem_zpowers F h7 hc hcfix)
  rcases zpow_eq_one_or_self_of_mul_self (L.z_mul_self D.val) n with h1 | h1
  · rw [h1] at hn
    rw [hvc, ← hn, mul_one]
  · rw [h1] at hn
    exact absurd (by rw [hvc, ← hn]) (D.fcomm_y_ne_mul_z F h7 h81 hY hij)

end CFSG.Quasithin.Fan86
