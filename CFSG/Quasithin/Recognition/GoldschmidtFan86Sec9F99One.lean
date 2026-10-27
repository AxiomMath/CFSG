module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F99Gen

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H} {xb t ub : H}
  {zm ym za' : Fin 3 → H}

theorem E1Ids.delta_odd (h : E1Ids w za y z xb t ub zm ym za') (hR : P1Rel x w za y z)
    (hC : P1cRel x za c y z) {c2 : H} {d1 d2 d3 d4 : ℕ}
    (hd1 : d1 ≤ 1) (hd3 : d3 ≤ 1)
    (hc2 : c2 = y 1 * y 3 * z 3 * c * z 0 ^ d1 * z 2 ^ d2 * z 4 ^ d3 * za ^ d4)
    (hB : c2⁻¹ * ym 2 * c2 = ym 2 * za) (hza : za ≠ 1) :
    (d1 = 0 ∧ d3 = 1) ∨ (d1 = 1 ∧ d3 = 0) := by
  have hz24 : Commute (z 2 ^ d2) (z 4 ^ d3) :=
    (commute_of_fcomm (hR.zz 2 4)).pow_pow d2 d3
  have hsplit : c2 = (y 1 * y 3 * z 3 * c * z 0 ^ d1 * z 4 ^ d3) * (z 2 ^ d2 * za ^ d4) := by
    rw [hc2]
    simp only [mul_assoc]
    rw [hz24.left_comm]
  have hq2 : z 2 * ym 2 = ym 2 * z 2 := by idc0 h hR hC
  have hqa : za * ym 2 = ym 2 * za := by idc0 h hR hC
  have hQ : (z 2 ^ d2 * za ^ d4) * ym 2 = ym 2 * (z 2 ^ d2 * za ^ d4) := comm_powmul hq2 hqa d2 d4
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd1 with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd3 with rfl | rfl
  · have hN : (y 1 * y 3 * z 3 * c * z 0 ^ 0 * z 4 ^ 0)⁻¹ * ym 2 *
        (y 1 * y 3 * z 3 * c * z 0 ^ 0 * z 4 ^ 0) = ym 2 := by idc0 h hR hC
    have h1 := conj_tail hQ hN
    rw [← hsplit, hB] at h1
    exact absurd (eq_one_of_eq_mul h1.symm) hza
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · have hN : (y 1 * y 3 * z 3 * c * z 0 ^ 1 * z 4 ^ 1)⁻¹ * ym 2 *
        (y 1 * y 3 * z 3 * c * z 0 ^ 1 * z 4 ^ 1) = ym 2 := by idc0 h hR hC
    have h1 := conj_tail hQ hN
    rw [← hsplit, hB] at h1
    exact absurd (eq_one_of_eq_mul h1.symm) hza

theorem E1Ids.c2_pin (h : E1Ids w za y z xb t ub zm ym za') (hR : P1Rel x w za y z)
    (hC : P1cRel x za c y z) {w2 c2 : H} {b e d1 d2 d3 d4 : ℕ} (hd1 : d1 ≤ 1) (hd3 : d3 ≤ 1)
    (hw2 : w2 = y 3 * y 4 * z 3 * z 2 ^ b * za ^ e)
    (hc2 : c2 = y 1 * y 3 * z 3 * c * z 0 ^ d1 * z 2 ^ d2 * z 4 ^ d3 * za ^ d4)
    (hB : c2⁻¹ * ym 2 * c2 = ym 2 * za)
    (hdich : fcomm w2 c2 = 1 ∨ fcomm w2 c2 = z 2 * za) (hza : za ≠ 1) (hz2 : z 2 ≠ 1) :
    d1 = 0 ∧ d3 = 1 ∧ c2 = y 1 * y 3 * z 3 * z 4 * c * (z 2 ^ d2 * za ^ d4) ∧
      fcomm w2 c2 = 1 := by
  have hz2a : z 2 * za = za * z 2 := (commute_of_fcomm_one (hR.cent_z 2)).symm
  have hBw2 : z 2 * (y 3 * y 4 * z 3) = (y 3 * y 4 * z 3) * z 2 := by collc0 hR hC
  have hBwa : za * (y 3 * y 4 * z 3) = (y 3 * y 4 * z 3) * za := by collc0 hR hC
  have hu : (z 2 ^ b * za ^ e) * (y 3 * y 4 * z 3) = (y 3 * y 4 * z 3) * (z 2 ^ b * za ^ e) :=
    comm_powmul hBw2 hBwa b e
  have hvw : (z 2 ^ d2 * za ^ d4) * (y 3 * y 4 * z 3) = (y 3 * y 4 * z 3) * (z 2 ^ d2 * za ^ d4) :=
    comm_powmul hBw2 hBwa d2 d4
  have hw2' : w2 = (y 3 * y 4 * z 3) * (z 2 ^ b * za ^ e) := by
    rw [hw2]
    simp only [mul_assoc]
  have huv := comm_powmul_powmul hz2a b e d2 d4
  rcases h.delta_odd hR hC hd1 hd3 hc2 hB hza with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hBc2 : z 2 * (y 1 * y 3 * z 3 * z 4 * c) = (y 1 * y 3 * z 3 * z 4 * c) * z 2 := by
      collc0 hR hC
    have hBca : za * (y 1 * y 3 * z 3 * z 4 * c) = (y 1 * y 3 * z 3 * z 4 * c) * za := by
      collc0 hR hC
    have hc2' : c2 = (y 1 * y 3 * z 3 * z 4 * c) * (z 2 ^ d2 * za ^ d4) := by
      rw [hc2]
      simp only [pow_zero, pow_one, mul_one, mul_assoc]
      rw [((commute_of_fcomm (hR.zz 2 4)).pow_left d2).left_comm,
        (commute_of_fcomm (hC.zc 4)).symm.left_comm]
    have hf : fcomm w2 c2 = 1 := by
      rw [hw2', hc2', fcomm_mul_mul hu (comm_powmul hBc2 hBca b e) hvw
        (comm_powmul hBc2 hBca d2 d4) huv]
      collc0 hR hC
    exact ⟨rfl, rfl, hc2', hf⟩
  · exfalso
    have hBc2 : z 2 * (y 1 * y 3 * z 3 * z 0 * c) = (y 1 * y 3 * z 3 * z 0 * c) * z 2 := by
      collc0 hR hC
    have hBca : za * (y 1 * y 3 * z 3 * z 0 * c) = (y 1 * y 3 * z 3 * z 0 * c) * za := by
      collc0 hR hC
    have hc2' : c2 = (y 1 * y 3 * z 3 * z 0 * c) * (z 2 ^ d2 * za ^ d4) := by
      rw [hc2]
      simp only [pow_zero, pow_one, mul_one, mul_assoc]
      rw [(commute_of_fcomm (hC.zc 0)).symm.left_comm]
    have hf : fcomm w2 c2 = za := by
      rw [hw2', hc2', fcomm_mul_mul hu (comm_powmul hBc2 hBca b e) hvw
        (comm_powmul hBc2 hBca d2 d4) huv]
      collc0 hR hC
    exact fcomm_wrong hf hdich hza hz2

end CFSG.Quasithin.Fan86
