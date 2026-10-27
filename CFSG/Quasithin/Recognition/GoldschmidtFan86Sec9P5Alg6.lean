module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Ids

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H]

theorem conj_of_comm {a b : H} (h : b * a = a * b) : b⁻¹ * a * b = a := by
  rw [mul_assoc, ← h, inv_mul_cancel_left]

theorem fcomm_mul_central {a b d : H} (hda : d * a = a * d) (hdb : d * b = b * d) :
    fcomm a (b * d) = fcomm a b := by
  have h1 : a⁻¹ * d⁻¹ = d⁻¹ * a⁻¹ := by
    have := congrArg (·⁻¹) hda
    simpa using this
  have hd' : d * fcomm a b = fcomm a b * d := by
    have hc : Commute d (fcomm a b) :=
      ((((show Commute d a from hda).inv_right).mul_right
        ((show Commute d b from hdb).inv_right)).mul_right (show Commute d a from hda)).mul_right
        (show Commute d b from hdb)
    exact hc.eq
  calc fcomm a (b * d) = (a⁻¹ * d⁻¹) * b⁻¹ * a * b * d := by unfold fcomm; group
    _ = (d⁻¹ * a⁻¹) * b⁻¹ * a * b * d := by rw [h1]
    _ = d⁻¹ * fcomm a b * d := by unfold fcomm; group
    _ = fcomm a b := conj_of_comm hd'

variable {x w za c : H} {y z : Fin 5 → H}

theorem P1Rel.mul_za (hR : P1Rel x w za y z) : P1Rel x (w * za) za y z where
  x5 := hR.x5
  w4 := by
    have hwz : Commute w za := (commute_of_fcomm_one hR.cent_w : za * w = w * za).symm
    rw [hwz.mul_pow, hR.w4, show 4 = 2 * 2 from rfl, pow_mul, hR.za2, one_pow, mul_one]
  y2 := hR.y2
  z2 := hR.z2
  za2 := hR.za2
  xw := by
    have h1 : za * x ^ 2 = x ^ 2 * za :=
      (Commute.pow_right (show Commute za x from commute_of_fcomm_one hR.cent_x) 2).eq
    calc (w * za)⁻¹ * x * (w * za) = za⁻¹ * (w⁻¹ * x * w) * za := by group
      _ = za⁻¹ * x ^ 2 * za := by rw [hR.xw]
      _ = x ^ 2 := conj_of_comm h1
  xy := hR.xy
  xz := hR.xz
  wy := fun j => by
    calc (w * za)⁻¹ * y j * (w * za) = za⁻¹ * (w⁻¹ * y j * w) * za := by group
      _ = za⁻¹ * y (tauLab j) * za := by rw [hR.wy j]
      _ = y (tauLab j) := conj_of_comm (commute_of_fcomm_one (hR.cent_y (tauLab j)))
  wz := fun j => by
    calc (w * za)⁻¹ * z j * (w * za) = za⁻¹ * (w⁻¹ * z j * w) * za := by group
      _ = za⁻¹ * z (tauLab j) * za := by rw [hR.wz j]
      _ = z (tauLab j) := conj_of_comm (commute_of_fcomm_one (hR.cent_z (tauLab j)))
  yy := hR.yy
  yz := hR.yz
  zz := hR.zz
  prod_y := hR.prod_y
  prod_z := hR.prod_z
  cent_x := hR.cent_x
  cent_w := by
    refine fcomm_eq_one_iff.2 ?_
    rw [← mul_assoc, commute_of_fcomm_one hR.cent_w]
  cent_y := hR.cent_y
  cent_z := hR.cent_z

theorem P1cRel.mul_za (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    P1cRel x za (c * za) y z where
  c2 := by
    have hcz : Commute c za := (commute_of_fcomm_one hC.cza : za * c = c * za).symm
    rw [hcz.mul_pow, hC.c2, hR.za2, mul_one]
  yc := fun j => by
    rw [fcomm_mul_central (commute_of_fcomm_one (hR.cent_y j))
      (commute_of_fcomm_one hC.cza), hC.yc j]
  zc := fun j => by
    rw [fcomm_mul_central (commute_of_fcomm_one (hR.cent_z j))
      (commute_of_fcomm_one hC.cza), hC.zc j]
  xc := by
    rw [fcomm_mul_central (commute_of_fcomm_one hR.cent_x) (commute_of_fcomm_one hC.cza), hC.xc]
  cza := by
    refine fcomm_eq_one_iff.2 ?_
    rw [← mul_assoc, commute_of_fcomm_one hC.cza]

variable {xb t w2 ub : H} {zm ym za' : Fin 3 → H}

theorem P5Ids.normalize {e : ℕ} (h : P5Ids w za y z xb t w2 ub zm ym za' e e)
    (hR : P1Rel x w za y z) :
    P5Ids (w * za ^ e) za y z xb t (w2 * za' 1 ^ e) ub zm ym za' 0 0 := by
  have he : e = 0 ∨ e = 1 := Nat.le_one_iff_eq_zero_or_eq_one.1 h.e1le
  have hc : xb⁻¹ * za * xb = za' 1 := by simpa [h.za0] using h.xa 0
  refine
    { e1le := Nat.zero_le 1
      e2le := Nat.zero_le 1
      t_eq := h.t_eq
      xb3 := h.xb3
      xb_t := h.xb_t
      zm0 := h.zm0
      zm1 := h.zm1
      zm2 := ?_
      za0 := h.za0
      za1 := h.za1
      za2 := h.za2
      ym0 := h.ym0
      ym1 := h.ym1
      ym2 := h.ym2
      ub_eq := h.ub_eq
      w2_eq := ?_
      xz := h.xz
      xy := h.xy
      xa := h.xa
      xub := h.xub
      xw := ?_ }
  · rcases he with rfl | rfl
    · simpa using h.zm2
    · rw [h.zm2]
      congr 1
      coll hR
  · have := h.w2_eq
    rcases he with rfl | rfl
    · simpa using this
    · rw [this, h.za1]
      coll hR
  · rcases he with rfl | rfl
    · simpa using h.xw
    · calc xb⁻¹ * (w * za ^ 1) * xb = (xb⁻¹ * w * xb) * (xb⁻¹ * za * xb) := by group
        _ = w2 * za' 1 ^ 1 := by rw [h.xw, hc, pow_one]

end CFSG.Quasithin.Fan86
