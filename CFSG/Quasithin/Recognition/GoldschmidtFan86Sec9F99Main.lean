module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F99Cfg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F99One
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F99Zero

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {F : FanTree Γ G}
  {L : ZLab Γ G}

theorem fan_9_9 (h7 : Fan7 F L) (h8 : Fan8Parts F L) (h65 : Fan65 F) (h512 : Fan512 F L)
    (h92 : Fan92 F L) (h95 : Fan95 F L) (h96 : Fan96 F L) (h98 : Fan98 F L) : Fan99 F L := by
  intro S h4
  have h95d : Fan95d F L := h95.2.2.2
  have hR := S.p1RelOf F h7 h8 h65 h512 h92
  have hC := S.p1cRelOf F h7 h8 h65 h512 h92 h4
  have hB := S.cA_conj F h95d h96.2 h4
  have hdich := S.fcomm_cA_dich F h7 h8 h65 h512 h92 h95d h4
  obtain ⟨-, -, -, a4, -, a6, -⟩ := h95d S
  obtain ⟨d₁, d₂, d₃, d₄, hc⟩ := h95.2.1 S h4
  have hza := S.za_ne_one
  have hz2 := S.zMu1_two_ne_one F
  have pk1 : S.w * S.w = S.zEta13 * L.z S.α →
      (∃ f₁ f₂ : Fin 2, S.cA 1 = S.yEta 1 * S.yEta 3 * S.zMu1 3 * S.zMu1 4 * S.c *
        S.zNb 2 ^ (f₁ : ℕ) * S.zNb 0 ^ (f₂ : ℕ)) ∧ fcomm (S.wA 1) (S.cA 1) = 1 := by
    intro hsq
    obtain ⟨e₁, e₂, hw⟩ := (h98 S).1 hsq
    rw [a6, a4] at hw
    obtain ⟨-, -, hc', hf⟩ := (S.e1ids F h95d hsq).c2_pin hR hC (by omega) (by omega) hw hc hB
      hdich hza hz2
    refine ⟨⟨d₂, d₄, ?_⟩, hf⟩
    rw [hc', a6, a4]
    simp only [mul_assoc]
  have pk0 : S.w * S.w = S.zEta13 →
      (∃ f₁ f₂ : Fin 2, S.cA 1 = S.yEta 1 * S.yEta 3 * S.zMu1 3 * S.zMu1 0 * S.c *
        S.zNb 2 ^ (f₁ : ℕ) * S.zNb 0 ^ (f₂ : ℕ)) ∧ fcomm (S.wA 1) (S.cA 1) = 1 := by
    intro hsq
    obtain ⟨-, e₁, e₂, hw⟩ := (h98 S).2 hsq
    rw [a6, a4] at hw
    obtain ⟨-, -, hc', hf⟩ := (S.e0ids F h95d hsq).c2_pin hR hC (by omega) (by omega) hw hc hB
      hdich hza hz2
    refine ⟨⟨d₂, d₄, ?_⟩, hf⟩
    rw [hc', a6, a4]
    simp only [mul_assoc]
  refine ⟨fun hsq => (pk1 hsq).1, fun hsq => (pk0 hsq).1, ?_⟩
  rcases S.isW1.sq with hsq | hsq
  · exact (pk1 hsq).2
  · exact (pk0 hsq).2

end CFSG.Quasithin.Fan86
