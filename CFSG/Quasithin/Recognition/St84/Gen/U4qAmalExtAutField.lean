module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtend
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtAutRigid
import CFSG.GH74.GLS.Stage2.OddAut.HeisField

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par
open CFSG.Quasithin.H13.Sec53F.Unit (fieldAut)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem eq_refl_of_stdAut_eq_conj_u4 {d g : hypSU h 2 0} (hd : d ∈ parP h) (hg : g ∈ parP h)
    {ρ : K ≃+* K} (hρ : ∀ x ∈ radQ h, u4StdAut h d ρ x = g * x * g⁻¹) :
    ρ = RingEquiv.refl K := by
  obtain ⟨r, hr, A, t, ht, he⟩ :=
    exists_eq_mul_levHom_mul_of_mem_parP h ((parP h).mul_mem ((parP h).inv_mem hd) hg)
  have key : ∀ y : K, ρ y = slMat h A 1 1 * (u4PtKappaVal h t * y) := by
    intro y
    have h1 := hρ _ (syElt_mem y)
    rw [u4StdAut_apply] at h1
    have h2 : fieldAut h ρ (syElt h y) = (d⁻¹ * g) * syElt h y * (d⁻¹ * g)⁻¹ :=
      calc fieldAut h ρ (syElt h y) = d⁻¹ * (d * fieldAut h ρ (syElt h y) * d⁻¹) * d := by group
        _ = d⁻¹ * (g * syElt h y * g⁻¹) * d := by rw [h1]
        _ = (d⁻¹ * g) * syElt h y * (d⁻¹ * g)⁻¹ := by group
    rw [fieldAut_syElt_u4, he] at h2
    have h3 := congrArg yc h2
    rw [yc_of (coe_syElt (h := h) (ρ y)),
      (xc_yc_conj_mul_levHom_mul_u4 h hr ht A (coe_syElt (h := h) y)).2] at h3
    rw [h3, mul_zero, mul_zero, zero_add]
  have h1 := key 1
  rw [map_one, mul_one] at h1
  refine RingEquiv.ext fun y => ?_
  rw [key y, RingEquiv.refl_apply, ← mul_assoc, ← h1, one_mul]

theorem eq_refl_or_eq_bar_of_involutive_u4 (ρ : K ≃+* K) (hρ : ∀ x, ρ (ρ x) = x) :
    ρ = RingEquiv.refl K ∨ ∀ x, ρ x = h.bar x := by
  have hm1 := h.one_le
  obtain ⟨φ, hφ, hord, -, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega : 1 ≤ 2 * m) h.card
  obtain ⟨k, hk, hρk⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow Nat.prime_two
    (by omega : 1 ≤ 2 * m) h.card ρ
  have hpow : ∀ (n : ℕ) (a : K), (φ ^ n) a = a ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ', RingAut.mul_apply, ih, hφ, ← pow_mul, pow_succ]
  have hφk : φ ^ k = ρ := RingEquiv.ext fun a => by rw [hpow, hρk]
  have hρ2 : ρ * ρ = 1 := RingEquiv.ext fun a => hρ a
  have hdvd : 2 * m ∣ 2 * k := by
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    rw [mul_comm, pow_mul, hφk, sq, hρ2]
  obtain ⟨t, rfl⟩ := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hdvd
  have ht : t < 2 := Nat.lt_of_mul_lt_mul_left (a := m) (by rw [mul_comm m 2]; exact hk)
  interval_cases t
  · left
    exact RingEquiv.ext fun a => by rw [hρk, mul_zero, pow_zero, pow_one, RingEquiv.refl_apply]
  · right
    intro a
    rw [hρk, mul_one, h.bar_apply]

end CFSG.Quasithin.F112R.St84

end
