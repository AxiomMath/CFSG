module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Cfg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F99Gen

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {F : FanTree Γ G}
  {L : ZLab Γ G}

namespace Sec9Cfg

variable (S : Sec9Cfg L)

theorem cA_conj (F : FanTree Γ G) (h95 : Fan95d F L) (h96 : Fan96b F L)
    (h4 : Nat.card S.D.calpha = 4) :
    (S.cA 1)⁻¹ * S.yMu 2 * S.cA 1 = S.yMu 2 * L.z S.α := by
  have hids := S.baseIds F h95
  obtain ⟨-, -, -, a4, -⟩ := h95 S
  have h96b := (h96 S h4).2 1 (by decide)
  have e1 : S.xβ⁻¹ * S.yMu 1 * S.xβ = S.yMu 2 := hids.xy 1
  have e2 : S.xβ⁻¹ * S.zNb 2 * S.xβ = L.z S.α := by
    have h := hids.xa 2
    have e : (2 : Fin 3) + 1 = 0 := by decide
    rw [e, a4] at h
    exact h
  calc (S.cA 1)⁻¹ * S.yMu 2 * S.cA 1
      = S.xβ⁻¹ * (S.c⁻¹ * S.yMu 1 * S.c) * S.xβ := by rw [S.cA_one, ← e1]; group
    _ = S.xβ⁻¹ * (S.yMu 1 * S.zNb 2) * S.xβ := by rw [h96b]
    _ = (S.xβ⁻¹ * S.yMu 1 * S.xβ) * (S.xβ⁻¹ * S.zNb 2 * S.xβ) := by group
    _ = S.yMu 2 * L.z S.α := by rw [e1, e2]

theorem fcomm_cA_dich (F : FanTree Γ G) (h7 : Fan7 F L) (h8 : Fan8Parts F L) (h65 : Fan65 F)
    (h512 : Fan512 F L) (h92 : Fan92 F L) (h95 : Fan95d F L) (h4 : Nat.card S.D.calpha = 4) :
    fcomm (S.wA 1) (S.cA 1) = 1 ∨ fcomm (S.wA 1) (S.cA 1) = S.zMu1 2 * L.z S.α := by
  have hids := S.baseIds F h95
  have hC := S.p1cRelOf F h7 h8 h65 h512 h92 h4
  have hc : S.c * S.c = L.z S.α := by rw [← pow_two]; exact hC.c2
  have h := fcomm_dich_conj (S.dichOf F h7 h8 h65 h512 h92 h4) hc S.xβ
  rw [S.wA_one, S.cA_one]
  rcases h with h | h
  · exact Or.inl h
  · right
    rw [h, hids.f911_conj.2.2, hids.za1]

end Sec9Cfg

end CFSG.Quasithin.Fan86
