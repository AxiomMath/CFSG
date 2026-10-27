module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Pres4
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Data3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G}

namespace Sec9Cfg

variable (S : Sec9Cfg L) (H : P5Hyp F L)

include H

theorem presData12 (hcard : Nat.card (MulAction.stabilizer G S.α) = 5 * 2 ^ 12)
    (h4 : Nat.card S.D.calpha = 4) {e d : ℕ} (he : e ≤ 1) (hd : d ≤ 1)
    (hid : P5Ids S.w (L.z S.α) S.yEta S.zMu1 S.xβ S.t (S.wA 1) S.ub S.zMu S.yMu S.zNb e e)
    (hcx : S.xβ⁻¹ * S.c * S.xβ = S.yEta 1 * S.yEta 3 * S.zMu1 3 * S.zMu1 4 * S.c *
      S.zMu1 2 ^ d * L.z S.α ^ 0) :
    PresData12 (MulAction.stabilizer G S.α) (MulAction.stabilizer G S.beta) S.D.x
      (S.w * L.z S.α ^ e) (L.z S.α) (S.c * L.z S.α ^ d) S.yEta S.zMu1 S.xβ S.t
      (S.w * L.z S.α ^ e) (S.wA 1 * S.zNb 1 ^ e) S.ub (S.c * L.z S.α ^ d) S.zMu S.yMu S.zNb := by
  have hR := S.p1Rel H
  have hC := S.p1cRel H h4
  have hwc := S.fcomm_wc H h4
  have hR' := hR.mul_za_pow he
  have hC' := P1cRel.mul_za_pow hR hC hd
  have hwc' := fcomm_norm hwc hR.cent_w hC.cza e d
  have hid' := hid.normalize hR
  obtain ⟨hza1, hz21, hz2za⟩ := S.z_ne H
  obtain ⟨-, hP⟩ := hid'.p2cRel913 hR' hC' hwc' (d₁ := 0) (d₂ := 0) (Nat.zero_le 1)
    (Nat.zero_le 1) (hid.hcx_norm hR hC hwc hd hcx) hza1 hz21 hz2za
  exact
    { memA := S.memA12 H e d, memB := S.memB12 H e d, memE := S.memE12 H d hid
      genA := S.genA12 H he hd hcard, genB := S.genB12 H he hd, genE := S.genE12 H he hd hid
      rA := hR', rAc := hC', rAwc := hwc', rB1 := hid'.p2Rel912 hR'
      rB1c := hid'.p2cRel912 hR' hC' hwc', rB2 := hid'.p2Rel913 hR', rB2c := hP
      l_t := hid'.t_eq.symm, l_w1 := rfl, l_w2 := hid'.link_w2, l_ub := hid'.link_ub hR'
      l_zm0 := hid'.zm0.symm, l_zm1 := hid'.link_zm1 hR', l_zm2 := hid'.link_zm2
      l_ym0 := hid'.ym0.symm, l_ym1 := hid'.link_ym1, l_ym2 := hid'.link_ym2
      l_za0 := hid'.za0.symm, l_za1 := hid'.za1.symm, l_za2 := hid'.za2.symm, l_c := rfl }

end Sec9Cfg

end CFSG.Quasithin.Fan86
