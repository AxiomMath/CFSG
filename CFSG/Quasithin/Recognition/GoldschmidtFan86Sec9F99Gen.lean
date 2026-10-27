module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Ids

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H]

theorem commute_of_fcomm {a b : H} (h : fcomm a b = 1) : Commute a b :=
  (commute_of_fcomm_one h).symm

theorem comm_powmul {p q N : H} (hp : p * N = N * p) (hq : q * N = N * q) (b e : ℕ) :
    (p ^ b * q ^ e) * N = N * (p ^ b * q ^ e) :=
  ((Commute.pow_left (show Commute p N from hp) b).mul_left
    (Commute.pow_left (show Commute q N from hq) e)).eq

theorem fcomm_mul_mul {a b u v : H} (hua : u * a = a * u) (hub : u * b = b * u)
    (hva : v * a = a * v) (hvb : v * b = b * v) (huv : u * v = v * u) :
    fcomm (a * u) (b * v) = fcomm a b := by
  have hubv : u * (b * v) = (b * v) * u := by
    rw [← mul_assoc, hub, mul_assoc, huv, ← mul_assoc]
  have h1 : fcomm (a * u) (b * v) = fcomm a (b * v) :=
    calc fcomm (a * u) (b * v) = (fcomm (b * v) (a * u))⁻¹ := fcomm_swap (b * v) (a * u)
      _ = (fcomm (b * v) a)⁻¹ := by rw [fcomm_mul_central hubv hua]
      _ = fcomm a (b * v) := by rw [fcomm_swap a (b * v), inv_inv]
  rw [h1, fcomm_mul_central hva hvb]

theorem fcomm_dich {w c za : H} (hd : fcomm w c = 1 ∨ w⁻¹ * c * w = c⁻¹) (hc : c * c = za) :
    fcomm w c = 1 ∨ fcomm w c = za := by
  rcases hd with h | h
  · exact Or.inl h
  · right
    calc fcomm w c = (w⁻¹ * c * w)⁻¹ * c := by unfold fcomm; group
      _ = c * c := by rw [h, inv_inv]
      _ = za := hc

theorem fcomm_dich_conj {w c za : H} (hd : fcomm w c = 1 ∨ w⁻¹ * c * w = c⁻¹) (hc : c * c = za)
    (g : H) :
    fcomm (g⁻¹ * w * g) (g⁻¹ * c * g) = 1 ∨ fcomm (g⁻¹ * w * g) (g⁻¹ * c * g) = g⁻¹ * za * g := by
  have e : fcomm (g⁻¹ * w * g) (g⁻¹ * c * g) = g⁻¹ * fcomm w c * g := by unfold fcomm; group
  rcases fcomm_dich hd hc with h | h
  · left
    rw [e, h]
    group
  · right
    rw [e, h]

theorem comm_powmul_powmul {p q : H} (hpq : p * q = q * p) (b e d f : ℕ) :
    (p ^ b * q ^ e) * (p ^ d * q ^ f) = (p ^ d * q ^ f) * (p ^ b * q ^ e) := by
  have h : Commute p q := hpq
  have c1 : Commute (p ^ b) (p ^ d) := (Commute.refl p).pow_pow b d
  have c2 : Commute (p ^ b) (q ^ f) := h.pow_pow b f
  have c3 : Commute (q ^ e) (p ^ d) := h.symm.pow_pow e d
  have c4 : Commute (q ^ e) (q ^ f) := (Commute.refl q).pow_pow e f
  exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq

theorem fcomm_wrong {f za z2 : H} (hf : f = za) (hd : f = 1 ∨ f = z2 * za) (hza : za ≠ 1)
    (hz2 : z2 ≠ 1) : False := by
  rcases hd with h | h
  · exact hza (hf.symm.trans h)
  · exact hz2 (mul_right_cancel (b := za) (by rw [one_mul]; exact (hf.symm.trans h).symm))

end CFSG.Quasithin.Fan86
