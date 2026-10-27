module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Pres3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Data3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G}

namespace Sec9Cfg

variable (S : Sec9Cfg L) (H : P5Hyp F L)

include H

theorem presData11 (hS : S.Star) (hcard : Nat.card (MulAction.stabilizer G S.α) = 5 * 2 ^ 11)
    (h2 : Nat.card S.D.calpha = 2) {e : ℕ} (he : e ≤ 1)
    (hid : P5Ids S.w (L.z S.α) S.yEta S.zMu1 S.xβ S.t (S.wA 1) S.ub S.zMu S.yMu S.zNb e e) :
    PresData11 (MulAction.stabilizer G S.α) (MulAction.stabilizer G S.beta) S.D.x
      (S.w * L.z S.α ^ e) (L.z S.α) S.yEta S.zMu1 S.xβ S.t (S.w * L.z S.α ^ e)
      (S.wA 1 * S.zNb 1 ^ e) S.ub S.zMu S.yMu S.zNb := by
  have hR' := (S.p1Rel H).mul_za_pow he
  have hid' := hid.normalize (S.p1Rel H)
  have hcza := S.c_eq_za H hS h2
  exact
    { memA := S.memA11 H e, memB := S.memB11 H e, memE := S.memE11 H hid
      genA := S.genA11 H he hcard, genB := S.genB11 H he hcza, genE := S.genE11 H he hcza hid
      rA := hR', rB1 := hid'.p2Rel912 hR', rB2 := hid'.p2Rel913 hR', l_t := hid'.t_eq.symm
      l_w1 := rfl, l_w2 := hid'.link_w2, l_ub := hid'.link_ub hR', l_zm0 := hid'.zm0.symm
      l_zm1 := hid'.link_zm1 hR', l_zm2 := hid'.link_zm2, l_ym0 := hid'.ym0.symm
      l_ym1 := hid'.link_ym1, l_ym2 := hid'.link_ym2, l_za0 := hid'.za0.symm
      l_za1 := hid'.za1.symm, l_za2 := hid'.za2.symm }

end Sec9Cfg

end CFSG.Quasithin.Fan86
