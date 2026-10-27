module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg3

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H} {xb t w2 ub : H}
  {zm ym za' : Fin 3 → H} {e₁ e₂ : ℕ}
  (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) (hR : P1Rel x w za y z)
  (hC : P1cRel x za c y z)

namespace P5Ids

include h hR hC

theorem p4_ct (_hwc : fcomm w c = 1) : t⁻¹ * c * t = c * zm 0 := by idcc h hR hC _hwc

theorem p4_w2c_00 (_hwc : fcomm w c = 1) (h1 : e₁ = 0) (h2 : e₂ = 0) :
    fcomm w2 c = ym 0 * za' 1 := by
  simp only [h.w2_eq, h1, h2]; idcc h hR hC _hwc

theorem p4_w2c_01 (_hwc : fcomm w c = 1) (h1 : e₁ = 0) (h2 : e₂ = 1) :
    fcomm w2 c = ym 0 * za' 1 := by
  simp only [h.w2_eq, h1, h2]; idcc h hR hC _hwc

theorem p4_w2c_10 (_hwc : fcomm w c = 1) (h1 : e₁ = 1) (h2 : e₂ = 0) :
    fcomm w2 c = ym 0 * za' 1 := by
  simp only [h.w2_eq, h1, h2]; idcc h hR hC _hwc

theorem p4_w2c_11 (_hwc : fcomm w c = 1) (h1 : e₁ = 1) (h2 : e₂ = 1) :
    fcomm w2 c = ym 0 * za' 1 := by
  simp only [h.w2_eq, h1, h2]; idcc h hR hC _hwc

theorem p4_w2c (_hwc : fcomm w c = 1) : fcomm w2 c = ym 0 * za' 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h.e1le with h1 | h1 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h.e2le with h2 | h2
  exacts [h.p4_w2c_00 hR hC _hwc h1 h2, h.p4_w2c_01 hR hC _hwc h1 h2,
    h.p4_w2c_10 hR hC _hwc h1 h2, h.p4_w2c_11 hR hC _hwc h1 h2]

theorem p4_cx0_0 (_hwc : fcomm w c = 1) {d : ℕ} (h1 : d = 0) :
    y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d * za ^ 0 = zm 2 * zm 1 * ym 2 * c * za' 2 ^ (d + 1) := by
  simp only [h1, Nat.reduceAdd]; idcc h hR hC _hwc

theorem p4_cx0_1 (_hwc : fcomm w c = 1) {d : ℕ} (h1 : d = 1) :
    y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d * za ^ 0 = zm 2 * zm 1 * ym 2 * c * za' 2 ^ (d + 1) := by
  simp only [h1, Nat.reduceAdd]; idcc h hR hC _hwc

theorem p4_cx0 (_hwc : fcomm w c = 1) {d : ℕ} (hd : d ≤ 1) :
    y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d * za ^ 0 = zm 2 * zm 1 * ym 2 * c * za' 2 ^ (d + 1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with h1 | h1
  exacts [h.p4_cx0_0 hR hC _hwc h1, h.p4_cx0_1 hR hC _hwc h1]

theorem p4_L1_0 (_hwc : fcomm w c = 1) {d : ℕ} (h1 : d = 0) :
    t⁻¹ * (y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d * za ^ 1) * t =
      zm 1 * zm 2 * (ym 1 * za' 1) * (c * zm 0) * za' 1 ^ (d + 1) * za' 0 ^ 1 := by
  simp only [h1, Nat.reduceAdd]; idcc h hR hC _hwc

theorem p4_L1_1 (_hwc : fcomm w c = 1) {d : ℕ} (h1 : d = 1) :
    t⁻¹ * (y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d * za ^ 1) * t =
      zm 1 * zm 2 * (ym 1 * za' 1) * (c * zm 0) * za' 1 ^ (d + 1) * za' 0 ^ 1 := by
  simp only [h1, Nat.reduceAdd]; idcc h hR hC _hwc

theorem p4_L1 (_hwc : fcomm w c = 1) {d : ℕ} (hd : d ≤ 1) :
    t⁻¹ * (y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d * za ^ 1) * t =
      zm 1 * zm 2 * (ym 1 * za' 1) * (c * zm 0) * za' 1 ^ (d + 1) * za' 0 ^ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with h1 | h1
  exacts [h.p4_L1_0 hR hC _hwc h1, h.p4_L1_1 hR hC _hwc h1]

variable (hwc : fcomm w c = 1)

include hwc

theorem p4_L2_0 {d : ℕ} (h1 : d = 0) :
    zm 2 * zm 0 * (ym 2 * za' 2) * ((y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d * za ^ 1) * zm 1) *
      za' 2 ^ (d + 1) * za' 1 ^ 1 = c * zm 0 * z 2 ^ 1 := by
  simp only [h1, Nat.reduceAdd]; idcc h hR hC hwc

theorem p4_L2_1 {d : ℕ} (h1 : d = 1) :
    zm 2 * zm 0 * (ym 2 * za' 2) * ((y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d * za ^ 1) * zm 1) *
      za' 2 ^ (d + 1) * za' 1 ^ 1 = c * zm 0 * z 2 ^ 1 := by
  simp only [h1, Nat.reduceAdd]; idcc h hR hC hwc

theorem p4_L2 {d : ℕ} (hd : d ≤ 1) :
    zm 2 * zm 0 * (ym 2 * za' 2) * ((y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d * za ^ 1) * zm 1) *
      za' 2 ^ (d + 1) * za' 1 ^ 1 = c * zm 0 * z 2 ^ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with h1 | h1
  exacts [h.p4_L2_0 hR hC hwc h1, h.p4_L2_1 hR hC hwc h1]

theorem p4_d2 {d₁ d₂ : ℕ} (hd₁ : d₁ ≤ 1) (hd₂ : d₂ ≤ 1)
    (hcx : xb⁻¹ * c * xb = y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d₁ * za ^ d₂) (hz2 : z 2 ≠ 1) :
    d₂ = 0 := by
  by_contra hne
  obtain rfl : d₂ = 1 := by omega
  have hdual : xb⁻¹ * (t⁻¹ * (xb⁻¹ * c * xb) * t) * xb = c * zm 0 := by
    rw [conj_dual h.xb_t c, h.p4_ct hR hC hwc]
  rw [hcx, h.p4_L1 hR hC hwc hd₁] at hdual
  simp only [conj_mul', p3_conj_pow, h.xz, h.xy, h.xa, Fin.reduceAdd] at hdual
  rw [hcx] at hdual
  have h2 := h.p4_L2 hR hC hwc hd₁
  rw [hdual] at h2
  exact hz2 (by simpa using left_eq_mul.1 h2)

theorem p4_main {d₁ d₂ : ℕ} (hd₁ : d₁ ≤ 1) (hd₂ : d₂ ≤ 1)
    (hcx : xb⁻¹ * c * xb = y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d₁ * za ^ d₂) (hz2 : z 2 ≠ 1) :
    d₂ = 0 ∧ P2cRel913 d₁ xb t w w2 c zm ym za' := by
  have hd := h.p4_d2 hR hC hwc hd₁ hd₂ hcx hz2
  subst hd
  refine ⟨rfl, ?_⟩
  exact
    { cx := hcx.trans (h.p4_cx0 hR hC hwc hd₁)
      ct := h.p4_ct hR hC hwc
      w1c := hwc
      w2c := h.p4_w2c hR hC hwc }

theorem p2cRel913 {d₁ d₂ : ℕ} (hd₁ : d₁ ≤ 1) (hd₂ : d₂ ≤ 1)
    (hcx : xb⁻¹ * c * xb = y 1 * y 3 * z 3 * z 4 * c * z 2 ^ d₁ * za ^ d₂)
    (_hza : za ≠ 1) (hz2 : z 2 ≠ 1) (_hzz : z 2 ≠ za) :
    d₂ = 0 ∧ P2cRel913 d₁ xb t w w2 c zm ym za' :=
  h.p4_main hR hC hwc hd₁ hd₂ hcx hz2

end P5Ids

end CFSG.Quasithin.Fan86
