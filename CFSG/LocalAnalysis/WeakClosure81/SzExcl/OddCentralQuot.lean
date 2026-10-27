module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsGrp
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenFischerLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SzExcl

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {X : Type} [Group X]

theorem fusionZStar_le_center [Finite X] (hO2 : CFSG.pCore 2 X = ⊥)
    (hodd : fusionOddCore X ≤ Subgroup.center X) : fusionZStar X ≤ Subgroup.center X :=
  (seven_k_grp_fusionZStar_le_fusionOddCore hO2 hodd).trans hodd

theorem odd_card_fusionZStar [Finite X] (hO2 : CFSG.pCore 2 X = ⊥)
    (hodd : fusionOddCore X ≤ Subgroup.center X) : Odd (Nat.card (fusionZStar X)) :=
  (OddCoreLiftF.odd_card_fusionOddCore X).of_dvd_nat
    (Subgroup.card_dvd_of_le (seven_k_grp_fusionZStar_le_fusionOddCore hO2 hodd))

theorem eq_of_mul_self_of_inv_mul_mem {Z : Subgroup X} (hZc : Z ≤ Subgroup.center X)
    (hZodd : Odd (Nat.card Z)) {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a⁻¹ * b ∈ Z) : a = b := by
  set z : X := a⁻¹ * b with hzdef
  have hzZ : z ∈ Z := by rw [hzdef]; exact hab
  have hcomm : Commute a z := Subgroup.mem_center_iff.mp (hZc hzZ) a
  have hb' : b = a * z := by
    rw [hzdef]
    exact (mul_inv_cancel_left a b).symm
  have hzz : z * z = 1 := by
    have h1 : (a * z) * (a * z) = z * z := by
      calc (a * z) * (a * z)
          = a * (z * (a * z)) := by rw [mul_assoc]
        _ = a * ((z * a) * z) := by rw [mul_assoc z a z]
        _ = a * ((a * z) * z) := by rw [← hcomm]
        _ = a * (a * (z * z)) := by rw [mul_assoc a z z]
        _ = (a * a) * (z * z) := by rw [← mul_assoc]
        _ = z * z := by rw [ha, one_mul]
    simpa [hb', h1] using hb
  have hz1 : z = 1 :=
    OddCoreLiftF.eq_one_of_two_elem_mem hZodd hzZ (i := 1) (by simpa [pow_two] using hzz)
  rw [hz1, mul_one] at hb'
  exact hb'.symm

theorem commute_of_mk_commute {Z : Subgroup X} [Z.Normal] (hZc : Z ≤ Subgroup.center X)
    (hZodd : Odd (Nat.card Z)) {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a : X ⧸ Z) * (b : X ⧸ Z) = (b : X ⧸ Z) * (a : X ⧸ Z)) :
    a * b = b * a := by
  have hcoe : ((a * b * a⁻¹ : X) : X ⧸ Z) =
      (a : X ⧸ Z) * (b : X ⧸ Z) * (a : X ⧸ Z)⁻¹ := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hq : ((a * b * a⁻¹ : X) : X ⧸ Z) = (b : X ⧸ Z) := by
    rw [hcoe, hab]
    group
  have hmem : b⁻¹ * (a * b * a⁻¹) ∈ Z := QuotientGroup.eq.mp hq.symm
  have hc : (a * b * a⁻¹) * (a * b * a⁻¹) = 1 := by
    have hconj : (MulAut.conj a) b = a * b * a⁻¹ := by rw [MulAut.conj_apply]
    rw [← hconj, ← map_mul, hb, map_one]
  have hba : b = a * b * a⁻¹ :=
    eq_of_mul_self_of_inv_mul_mem hZc hZodd hb hc hmem
  calc a * b = (a * b * a⁻¹) * a := by group
    _ = b * a := by rw [← hba]

theorem pow_card_mul_self_eq {Z : Subgroup X} (hZc : Z ≤ Subgroup.center X)
    (hZodd : Odd (Nat.card Z)) {t g : X} (ht : t * t = 1)
    (hg : t⁻¹ * (g * g) ∈ Z) : g ^ Nat.card Z * g ^ Nat.card Z = t := by
  obtain ⟨k, hk⟩ := hZodd
  set z : X := t⁻¹ * (g * g) with hzdef
  have hzZ : z ∈ Z := by rw [hzdef]; exact hg
  have htz : Commute t z := Subgroup.mem_center_iff.mp (hZc hzZ) t
  have hgg : g * g = t * z := by
    rw [hzdef]
    exact (mul_inv_cancel_left t (g * g)).symm
  have ht2 : t ^ 2 = 1 := by rw [pow_two, ht]
  have htm : t ^ (2 * k + 1) = t := by
    rw [pow_succ, pow_mul, ht2, one_pow, one_mul]
  have hzm : z ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact OddCoreLiftF.pow_card_eq_one_of_mem hzZ
  have hmain : (g * g) ^ (2 * k + 1) = t := by
    rw [hgg, htz.mul_pow, htm, hzm, mul_one]
  rw [hk, ← (Commute.refl g).mul_pow (2 * k + 1)]
  exact hmain

theorem not_mem_of_mul_self {Z : Subgroup X} (hZodd : Odd (Nat.card Z)) {t : X}
    (ht : t * t = 1) (ht1 : t ≠ 1) : t ∉ Z := by
  intro hmem
  exact ht1 (OddCoreLiftF.eq_one_of_two_elem_mem hZodd hmem (i := 1)
    (by simpa [pow_two] using ht))

end CFSG.LocalAnalysis.WeakClosure81.SzExcl
