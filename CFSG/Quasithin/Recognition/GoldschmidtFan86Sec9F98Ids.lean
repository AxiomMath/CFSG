module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg6
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Coll
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg1c

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H]

structure IdsBase (w za : H) (y z : Fin 5 → H) (xb t ub : H) (zm ym za' : Fin 3 → H) : Prop where
  t_eq : t = y 0
  zm0 : zm 0 = z 0
  zm1 : zm 1 = t⁻¹ * zm 2 * t
  za0 : za' 0 = za
  za1 : za' 1 = z 2 * za
  za2 : za' 2 = z 2
  ym0 : ym 0 = z 0 * z 1
  ym1 : ym 1 = ym 0 * ym 2
  ub_eq : ub = z 1 * z 3 * za
  xz : ∀ i, xb⁻¹ * zm i * xb = zm (i + 1)
  xy : ∀ i, xb⁻¹ * ym i * xb = ym (i + 1)
  xa : ∀ i, xb⁻¹ * za' i * xb = za' (i + 1)

structure E1Ids (w za : H) (y z : Fin 5 → H) (xb t ub : H) (zm ym za' : Fin 3 → H) : Prop
    extends IdsBase w za y z xb t ub zm ym za' where
  zm2 : zm 2 = w * w * za
  ym2 : ym 2 = y 2 * za' 2

structure E0Ids (w za : H) (y z : Fin 5 → H) (xb t ub : H) (zm ym za' : Fin 3 → H) : Prop
    extends IdsBase w za y z xb t ub zm ym za' where
  zm2 : zm 2 = w * w
  ym2 : ym 2 = y 2 * ub * za' 2

macro "idc2 " h:term:max hR:term:max hC:term:max hww:term:max : tactic =>
  `(tactic| (simp only [($h).t_eq, ($h).zm0, ($h).zm1, ($h).zm2, ($h).za0, ($h).za1, ($h).za2,
      ($h).ym0, ($h).ym1, ($h).ym2, ($h).ub_eq, swap12_zero, swap12_one, swap12_two,
      fin3_neg_add_01, fin3_neg_add_02, fin3_neg_add_10, fin3_neg_add_12, fin3_neg_add_20,
      fin3_neg_add_21]; try collc2 $hR $hC $hww))

macro "idc0 " h:term:max hR:term:max hC:term:max : tactic =>
  `(tactic| (simp only [($h).t_eq, ($h).zm0, ($h).zm1, ($h).zm2, ($h).za0, ($h).za1, ($h).za2,
      ($h).ym0, ($h).ym1, ($h).ym2, ($h).ub_eq, swap12_zero, swap12_one, swap12_two,
      fin3_neg_add_01, fin3_neg_add_02, fin3_neg_add_10, fin3_neg_add_12, fin3_neg_add_20,
      fin3_neg_add_21]; try collc0 $hR $hC))

theorem conj_tail {P Q M N : H} (hQ : Q * N = N * Q) (hP : P⁻¹ * M * P = N) :
    (P * Q)⁻¹ * M * (P * Q) = N := by
  calc (P * Q)⁻¹ * M * (P * Q) = Q⁻¹ * (P⁻¹ * M * P) * Q := by group
    _ = Q⁻¹ * N * Q := by rw [hP]
    _ = N := conj_of_comm hQ

theorem eq_one_of_eq_mul {a b : H} (h : a = a * b) : b = 1 :=
  mul_left_cancel (a := a) (by rw [mul_one]; exact h.symm)

variable {x w za : H} {y z : Fin 5 → H} {xb t ub : H} {zm ym za' : Fin 3 → H}

namespace IdsBase

variable (h : IdsBase w za y z xb t ub zm ym za')

include h

theorem f911_conj :
    xb⁻¹ * z 0 * xb = zm 1 ∧ xb⁻¹ * ym 0 * xb = ym 1 ∧ xb⁻¹ * za * xb = za' 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [h.zm0] using h.xz 0
  · simpa using h.xy 0
  · simpa [h.za0] using h.xa 0

theorem f911 (hR : P1Rel x w za y z) (hub : xb⁻¹ * ub * xb = ub) :
    xb⁻¹ * z 3 * xb = zm 1 * ym 1 * ub * za' 1 := by
  obtain ⟨e1, e2, e3⟩ := h.f911_conj
  have h3 : z 3 = (z 0 * (z 0 * z 1)) * ub * za := by rw [h.ub_eq]; coll hR
  calc xb⁻¹ * z 3 * xb = xb⁻¹ * ((z 0 * (z 0 * z 1)) * ub * za) * xb := by rw [h3]
    _ = (xb⁻¹ * z 0 * xb) * (xb⁻¹ * (z 0 * z 1) * xb) * (xb⁻¹ * ub * xb) * (xb⁻¹ * za * xb) := by
        group
    _ = zm 1 * ym 1 * ub * za' 1 := by
        rw [e1, e3, hub, ← h.ym0, e2]

theorem key (hR : P1Rel x w za y z) (hub : xb⁻¹ * ub * xb = ub) {w2 : H}
    (hxw : xb⁻¹ * w * xb = w2) : w2⁻¹ * zm 1 * w2 = zm 1 * ym 1 * ub * za' 1 := by
  have hz : z 3 = w⁻¹ * z 0 * w := by
    have := hR.wz 0
    have e : tauLab 0 = 3 := by decide
    rw [e] at this
    exact this.symm
  have hc : xb⁻¹ * z 3 * xb = w2⁻¹ * (xb⁻¹ * z 0 * xb) * w2 := by
    rw [hz, ← hxw]
    group
  rw [← h.f911 hR hub, hc, h.f911_conj.1]

end IdsBase

end CFSG.Quasithin.Fan86
