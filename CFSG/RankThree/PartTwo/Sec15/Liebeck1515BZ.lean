module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515

variable {G : Type*} [Group G]

private theorem pow_three_mem_of_mem_sup_zpowers {D : Subgroup G} {c : G}
    (hcD : c ∈ Subgroup.normalizer (D : Set G)) (hc3 : c ^ 3 = 1) {z : G}
    (hz : z ∈ D ⊔ Subgroup.zpowers c) : z ^ 3 ∈ D := by
  have hCD : Subgroup.zpowers c ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.zpowers_le.mpr hcD
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D _ hCD] at hz
  obtain ⟨d, hd, y, hy, rfl⟩ := Set.mem_mul.mp hz
  have hy3 : y ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_mem_zpowers hy).trans (orderOf_dvd_of_pow_eq_one hc3))
  have hyD : y ∈ Subgroup.normalizer (D : Set G) := hCD hy
  have h1 : y * d * y⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hyD d).mp hd
  have h2 : y * (y * d * y⁻¹) * y⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hyD _).mp h1
  have h3 : (d * y) ^ 3 = d * (y * d * y⁻¹) * (y * (y * d * y⁻¹) * y⁻¹) * y ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [h3, hy3, mul_one]
  exact mul_mem (mul_mem hd h1) h2

private theorem mem_of_pow_three_mem {D : Subgroup G} {z : G} (h3 : z ^ 3 ∈ D)
    (hz : ¬ 3 ∣ orderOf z) : z ∈ D := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hz)
  exact hm ▸ pow_mem h3 m

private theorem conj_mem_sup {E EZ R : Subgroup G} {c : G} (hcE : c ∈ E)
    (hEZn : E ≤ Subgroup.normalizer (EZ : Set G)) (hRE : R ≤ E)
    (hRn : E ≤ Subgroup.normalizer (R : Set G)) (hcomm : ⁅EZ, R⁆ = ⊥)
    (hdec : E ≤ EZ ⊔ (R ⊔ Subgroup.zpowers c)) {e : G} (he : e ∈ E) :
    e * c * e⁻¹ ∈ (R ⊔ ⁅EZ, Subgroup.zpowers c⁆) ⊔ Subgroup.zpowers c := by
  have hCE : Subgroup.zpowers c ≤ E := Subgroup.zpowers_le.mpr hcE
  have hRC : R ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (EZ : Set G) :=
    sup_le (hRE.trans hEZn) (hCE.trans hEZn)
  have hCR : Subgroup.zpowers c ≤ Subgroup.normalizer (R : Set G) := hCE.trans hRn
  have he' := hdec he
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left EZ _ hRC] at he'
  obtain ⟨z, hz, x, hx, rfl⟩ := Set.mem_mul.mp he'
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R _ hCR] at hx
  obtain ⟨r, hr, y, hy, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hcr : c * r⁻¹ * c⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hRn hcE) r⁻¹).mp (inv_mem hr)
  have hr' : r * (c * r⁻¹ * c⁻¹) ∈ R := mul_mem hr hcr
  have hcom : Commute z (r * (c * r⁻¹ * c⁻¹)) := by
    have h := Subgroup.commutator_mem_commutator hz hr'
    rwa [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at h
  have hzc : z * c * z⁻¹ * c⁻¹ ∈ ⁅EZ, Subgroup.zpowers c⁆ :=
    Subgroup.commutator_mem_commutator hz (Subgroup.mem_zpowers c)
  have hL : z * (r * c ^ k) * c * (z * (r * c ^ k))⁻¹ = z * r * c * r⁻¹ * z⁻¹ := by group
  have hR : r * (c * r⁻¹ * c⁻¹) * (z * c * z⁻¹ * c⁻¹) * c = z * r * c * r⁻¹ * z⁻¹ :=
    calc r * (c * r⁻¹ * c⁻¹) * (z * c * z⁻¹ * c⁻¹) * c
        = r * (c * r⁻¹ * c⁻¹) * z * c * z⁻¹ := by group
      _ = z * (r * (c * r⁻¹ * c⁻¹)) * c * z⁻¹ := by rw [← hcom.eq]
      _ = z * r * c * r⁻¹ * z⁻¹ := by group
  rw [hL, ← hR]
  exact mul_mem (Subgroup.mem_sup_left (mul_mem (Subgroup.mem_sup_left hr')
    (Subgroup.mem_sup_right hzc))) (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))

theorem eq_commutator_of_generated {E EZ R : Subgroup G} {c : G} (hcE : c ∈ E)
    (hc3 : orderOf c = 3)
    (hgen : E ≤ Subgroup.closure {x | ∃ e ∈ E, x = e * c * e⁻¹})
    (hEZE : EZ ≤ E) (hEZn : E ≤ Subgroup.normalizer (EZ : Set G)) (hEZ3 : ¬ 3 ∣ Nat.card EZ)
    (hRE : R ≤ E) (hRn : E ≤ Subgroup.normalizer (R : Set G))
    (hcomm : ⁅EZ, R⁆ = ⊥) (hEZR : EZ ⊓ R = ⊥)
    (hdec : E ≤ EZ ⊔ (R ⊔ Subgroup.zpowers c)) :
    EZ = ⁅EZ, Subgroup.zpowers c⁆ := by
  have hCE : Subgroup.zpowers c ≤ E := Subgroup.zpowers_le.mpr hcE
  have hWEZ : ⁅EZ, Subgroup.zpowers c⁆ ≤ EZ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hCE.trans hEZn)
  have hcW : c ∈ Subgroup.normalizer ((⁅EZ, Subgroup.zpowers c⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ _ (Subgroup.mem_zpowers c)
  have hcD : c ∈ Subgroup.normalizer ((R ⊔ ⁅EZ, Subgroup.zpowers c⁆ : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hRn hcE, hcW⟩
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hEgen : E ≤ (R ⊔ ⁅EZ, Subgroup.zpowers c⁆) ⊔ Subgroup.zpowers c := by
    refine hgen.trans ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨e, he, rfl⟩
    exact conj_mem_sup hcE hEZn hRE hRn hcomm hdec he
  have hEZD : EZ ≤ R ⊔ ⁅EZ, Subgroup.zpowers c⁆ := fun z hz =>
    mem_of_pow_three_mem (pow_three_mem_of_mem_sup_zpowers hcD hc3' (hEgen (hEZE hz)))
      fun h3 => hEZ3 (h3.trans (Subgroup.orderOf_dvd_natCard EZ hz))
  refine le_antisymm (fun z hz => ?_) hWEZ
  have hWR : ⁅EZ, Subgroup.zpowers c⁆ ≤ Subgroup.normalizer (R : Set G) :=
    hWEZ.trans (hEZE.trans hRn)
  have hzD := hEZD hz
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left R _ hWR] at hzD
  obtain ⟨r, hr, w, hw, rfl⟩ := Set.mem_mul.mp hzD
  have hrEZ : r ∈ EZ := by simpa using mul_mem hz (inv_mem (hWEZ hw))
  have hr1 : r = 1 := by
    have h : r ∈ EZ ⊓ R := ⟨hrEZ, hr⟩
    rwa [hEZR, Subgroup.mem_bot] at h
  simpa [hr1] using hw

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515
