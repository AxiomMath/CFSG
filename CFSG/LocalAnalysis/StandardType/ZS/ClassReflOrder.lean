module

public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelBasic
import CFSG.LocalAnalysis.StandardType.GGWitOrthSpin

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem zmod3_sq_eq_zero_or_one (t : ZMod 3) : t ^ 2 = 0 ∨ t ^ 2 = 1 := by
  fin_cases t <;> decide

private theorem zmod3_inv_mul_inv_mul_sq (c : ZMod 3) (hc : c ≠ 0) (t : ZMod 3) :
    c⁻¹ * c⁻¹ * t ^ 2 = 0 ∨ c⁻¹ * c⁻¹ * t ^ 2 = 4 := by
  have hc2 : c ^ 2 = 1 := by
    fin_cases c
    · exact absurd rfl hc
    · decide
    · decide
  rcases zmod3_sq_eq_zero_or_one t with ht | ht
  · left
    rw [ht, mul_zero]
  · right
    rw [ht]
    have hcinv : c⁻¹ * c⁻¹ = 1 := by
      rw [← mul_inv, ← pow_two, hc2, inv_one]
    rw [hcinv, one_mul]
    decide

private theorem classRefl_dual_apply_self {Q : QuadraticForm (ZMod p) U} {a : U}
    (ha : Q a ≠ 0) : ((Q a)⁻¹ • QuadraticMap.polarBilin Q a) a = 2 := by
  simp only [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
  rw [QuadraticMap.polar_self, two_smul]
  field_simp [ha]
  norm_num

private theorem module_reflection_comm_of_apply_eq_zero {φ ψ : Module.Dual (ZMod p) U} {a b : U}
    (hφa : φ a = 2) (hψb : ψ b = 2) (hφb : φ b = 0) (hψa : ψ a = 0) :
    Module.reflection hφa * Module.reflection hψb =
      Module.reflection hψb * Module.reflection hφa := by
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Module.reflection_apply,
    Module.reflection_apply, Module.reflection_apply, Module.reflection_apply,
    map_sub, map_smul, map_sub, map_smul, hφb, hψa, smul_zero]
  module

private theorem module_reflection_mul_order_le_two {φ ψ : Module.Dual (ZMod p) U} {a b : U}
    (hφa : φ a = 2) (hψb : ψ b = 2) (hφb : φ b = 0) (hψa : ψ a = 0) :
    orderOf (Module.reflection hφa * Module.reflection hψb) ≤ 2 := by
  have hcomm := module_reflection_comm_of_apply_eq_zero hφa hψb hφb hψa
  have hsq : (Module.reflection hφa * Module.reflection hψb) *
      (Module.reflection hφa * Module.reflection hψb) = 1 := by
    calc
      _ = Module.reflection hφa * (Module.reflection hψb * Module.reflection hφa) *
          Module.reflection hψb := by group
      _ = Module.reflection hφa * (Module.reflection hφa * Module.reflection hψb) *
          Module.reflection hψb := by rw [hcomm]
      _ = (Module.reflection hφa * Module.reflection hφa) *
          (Module.reflection hψb * Module.reflection hψb) := by group
      _ = 1 := by
        rw [show Module.reflection hφa * Module.reflection hφa = 1 by
              simpa [Module.reflection_inv] using mul_inv_cancel (Module.reflection hφa),
            show Module.reflection hψb * Module.reflection hψb = 1 by
              simpa [Module.reflection_inv] using mul_inv_cancel (Module.reflection hψb),
            mul_one]
  have hdvd : orderOf (Module.reflection hφa * Module.reflection hψb) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa [pow_two] using hsq
  exact Nat.le_of_dvd (by norm_num) hdvd

private theorem classRefl_reflect_eq_module_reflection {Q : QuadraticForm (ZMod p) U} {a : U}
    (ha : Q a ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a =
      Module.reflection (f := (Q a)⁻¹ • QuadraticMap.polarBilin Q a) (x := a) (by
        simp only [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
        rw [QuadraticMap.polar_self, two_smul]
        field_simp [ha]
        norm_num) := by
  ext v
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply ha, Module.reflection_apply,
    LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, smul_eq_mul, div_eq_inv_mul]

private theorem orderOf_reflection_mul_dvd_of_four (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2) (h4 : φ b * ψ a = 4) :
    orderOf (Module.reflection hφ * Module.reflection hψ) ∣ p := by
  rw [orderOf_dvd_iff_pow_eq_one]
  exact CFSG.StandardType.reflection_mul_reflection_pow_char hφ hψ
    ((Fact.out : p.Prime).odd_of_ne_two hp) h4

theorem mem_classRefl_of_isRefl_mem_closure (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0) {t : U ≃ₗ[ZMod p] U}
    (ht : t ∈ Subgroup.closure (ClassRefl p Q c)) (hrt : IsRefl p t) : t ∈ ClassRefl p Q c :=
  wit_classRefl_of_mem_closure Fact.out hp Q hQ c hc hrt ht

theorem orderOf_mul_le_three_of_classRefl_three (hp3 : p = 3) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0) {x y : U ≃ₗ[ZMod p] U}
    (hx : x ∈ Subgroup.closure (ClassRefl p Q c)) (hy : y ∈ Subgroup.closure (ClassRefl p Q c))
    (hrx : IsRefl p x) (hry : IsRefl p y) : orderOf (x * y) ≤ 3 := by
  subst p
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hxmem := mem_classRefl_of_isRefl_mem_closure hp2 hQ hc hx hrx
  have hymem := mem_classRefl_of_isRefl_mem_closure hp2 hQ hc hy hry
  obtain ⟨a, hQa, hxeq⟩ := (mem_classRefl_iff hp2 hQ hc x).mp hxmem
  obtain ⟨b, hQb, hyeq⟩ := (mem_classRefl_iff hp2 hQ hc y).mp hymem
  have hQane : Q a ≠ 0 := by rw [hQa]; exact hc
  have hQbne : Q b ≠ 0 := by rw [hQb]; exact hc
  let φ : Module.Dual (ZMod 3) U := (Q a)⁻¹ • QuadraticMap.polarBilin Q a
  let ψ : Module.Dual (ZMod 3) U := (Q b)⁻¹ • QuadraticMap.polarBilin Q b
  let t : ZMod 3 := QuadraticMap.polarBilin Q a b
  have hφa : φ a = 2 := by simpa only [φ] using classRefl_dual_apply_self hQane
  have hψb : ψ b = 2 := by simpa only [ψ] using classRefl_dual_apply_self hQbne
  have hsym : QuadraticMap.polarBilin Q b a = t := by
    simp only [t, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  have hφb_eq : φ b = (Q a)⁻¹ * t := by
    simp only [φ, LinearMap.smul_apply, smul_eq_mul, t]
  have hψa_eq : ψ a = (Q b)⁻¹ * t := by
    simp only [ψ, LinearMap.smul_apply, smul_eq_mul, hsym]
  have hprod : φ b * ψ a = c⁻¹ * c⁻¹ * t ^ 2 := by
    rw [hφb_eq, hψa_eq, hQa, hQb]
    ring
  have hxa : CFSG.ClassicalGroups.Orthogonal.reflect Q a = Module.reflection hφa := by
    simpa only [φ] using classRefl_reflect_eq_module_reflection hQane
  have hya : CFSG.ClassicalGroups.Orthogonal.reflect Q b = Module.reflection hψb := by
    simpa only [ψ] using classRefl_reflect_eq_module_reflection hQbne
  rw [hxeq, hyeq, hxa, hya]
  rcases zmod3_inv_mul_inv_mul_sq c hc t with hzero | hfour
  · have ht2 : t ^ 2 = 0 := by
      have hcne : c⁻¹ * c⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hc) (inv_ne_zero hc)
      exact (mul_eq_zero.mp hzero).resolve_left hcne
    have ht : t = 0 := by
      rw [pow_two] at ht2
      exact mul_self_eq_zero.mp ht2
    have hφb0 : φ b = 0 := by rw [hφb_eq, ht, mul_zero]
    have hψa0 : ψ a = 0 := by rw [hψa_eq, ht, mul_zero]
    exact le_trans (module_reflection_mul_order_le_two hφa hψb hφb0 hψa0) (by norm_num)
  · have hφψ : φ b * ψ a = 4 := by rw [hprod, hfour]
    have hdvd := orderOf_reflection_mul_dvd_of_four hp2 hφa hψb hφψ
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
