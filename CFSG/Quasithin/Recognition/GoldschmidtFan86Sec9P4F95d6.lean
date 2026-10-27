module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95d5

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_9_5d (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h82 : Fan82 F L) (h83 : Fan83 F L) (h85 : Fan85 F L) (h87 : Fan87 F L)
    (h512 : Fan512 F L) : Fan95d F L := fun S => by
  have h71c := h7.2.2.1
  have hR := S.p1Rel_of F h71c h82.1 h83.2.1 h83.2.2.2.1 h85
  have hprod := S.yMu_prod_eq_one F h71c h83.2.1 h83.2.2.2.1 h512 hR
  have hY1 := S.yMu_zero_mul_self F h71c
  have hY3 := S.yMu_two_mul_self F h71c
  refine ⟨S.zMu_zero, S.zMu_two, ?_, S.zNb_zero, ?_, S.zNb_two, ?_,
    fun hε => S.yMu_two_eps1 F h7 h83.1 h83.2.1 h83.2.2.2.1 h87 h512 hR hε,
    fun hε => S.yMu_two_eps0 F h7 h81 h82.1 h83.1 h83.2.1 h83.2.2.2.1 h87 h512 hR hε, ?_⟩
  · rw [S.t_inv h71c]
    exact S.zMu_one_eq h71c h81
  · rw [S.zNb_one_eq F h71c h512]
    exact (S.zMu1_comm_alpha F h71c 2).eq.symm
  · have hY1i : (S.yMu 0)⁻¹ = S.yMu 0 := inv_eq_of_mul_eq_one_right hY1
    have hY3i : (S.yMu 2)⁻¹ = S.yMu 2 := inv_eq_of_mul_eq_one_right hY3
    calc S.yMu 1 = (S.yMu 0)⁻¹ * (S.yMu 0 * S.yMu 1 * S.yMu 2) * (S.yMu 2)⁻¹ := by group
      _ = S.yMu 0 * S.yMu 2 := by rw [hprod, hY1i, hY3i]; group
  · rw [S.ub_eq, S.zNb_one_eq F h71c h512]
    coll hR

end CFSG.Quasithin.Fan86
