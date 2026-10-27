module

import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
import CFSG.LocalAnalysis.StandardType.ZS.ReflProductOrder
import CFSG.LocalAnalysis.StandardType.ZS.InitialPair
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.ReflFrame
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem conj_pairing {w u : U} {τ φ : Module.Dual (ZMod p) U} (hτ : τ w = 2) (hφ : φ u = 2) :
    (φ - φ w • τ) (u - τ u • w) = 2 := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, hτ, hφ]
  ring

theorem reflection_conj_reflection {w u : U} {τ φ : Module.Dual (ZMod p) U} (hτ : τ w = 2)
    (hφ : φ u = 2) :
    Module.reflection hτ * Module.reflection hφ * Module.reflection hτ =
      Module.reflection (conj_pairing hτ hφ) := by
  ext x
  simp only [LinearEquiv.mul_apply, Module.reflection_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, hτ]
  module

theorem smul_pairing {v : U} {φ : Module.Dual (ZMod p) U} (hφ : φ v = 2) {l : ZMod p}
    (hl : l ≠ 0) : (l⁻¹ • φ) (l • v) = 2 := by
  rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, hφ, ← mul_assoc,
    inv_mul_cancel₀ hl, one_mul]

theorem reflection_smul {v : U} {φ : Module.Dual (ZMod p) U} (hφ : φ v = 2) {l : ZMod p}
    (hl : l ≠ 0) : Module.reflection (smul_pairing hφ hl) = Module.reflection hφ := by
  ext x
  rw [Module.reflection_apply, Module.reflection_apply, LinearMap.smul_apply, smul_eq_mul,
    smul_smul, show l⁻¹ * φ x * l = φ x by field_simp]

theorem reflection_mul_comm_of_apply_eq_zero {u v : U} {φ ψ : Module.Dual (ZMod p) U}
    (hu : φ u = 2) (hv : ψ v = 2) (h1 : φ v = 0) (h2 : ψ u = 0) :
    Module.reflection hu * Module.reflection hv = Module.reflection hv * Module.reflection hu := by
  have h := reflection_mul_reflection_pow_two hu hv h1 h2
  rw [pow_two] at h
  calc Module.reflection hu * Module.reflection hv
      = (Module.reflection hu * Module.reflection hv)⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
    _ = Module.reflection hv * Module.reflection hu := by
        rw [mul_inv_rev, Module.reflection_inv, Module.reflection_inv]

theorem two_smul_eq_of_reflection_eq {u v : U} {φ ψ : Module.Dual (ZMod p) U} (hu : φ u = 2)
    (hv : ψ v = 2) (h : Module.reflection hu = Module.reflection hv) :
    ψ u • v = (2 : ZMod p) • u := by
  have h1 := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) h
  simp only [Module.reflection_apply, hu] at h1
  calc ψ u • v = u - (u - ψ u • v) := by abel
    _ = (2 : ZMod p) • u := by rw [← h1]; module

theorem eta_cases_of_orderOf_le_four [Module.Finite (ZMod p) U] (hp : p ≠ 2) {u v : U}
    {φ ψ : Module.Dual (ZMod p) U} (hu : φ u = 2) (hv : ψ v = 2)
    (h : orderOf (Module.reflection hu * Module.reflection hv) ≤ 4) :
    (φ v = 0 ∧ ψ u = 0) ∨ φ v * ψ u = 1 ∨ φ v * ψ u = 2 ∨
      (Module.reflection hu = Module.reflection hv ∧ φ v * ψ u = 4) := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) DFunLike.coe_injective
  have hpos := orderOf_pos (Module.reflection hu * Module.reflection hv)
  interval_cases hn : orderOf (Module.reflection hu * Module.reflection hv)
  · have h1 := orderOf_eq_one_iff.mp hn
    have heq : Module.reflection hu = Module.reflection hv := by
      rw [eq_inv_of_mul_eq_one_left h1, Module.reflection_inv]
    exact Or.inr (Or.inr (Or.inr ⟨heq, mul_eq_four_of_reflection_eq hu hv heq⟩))
  · exact Or.inl (apply_eq_zero_of_orderOf_eq_two hp hu hv hn)
  · exact Or.inr (Or.inl (apply_mul_apply_eq_one_of_orderOf_eq_three hp hu hv hn))
  · exact Or.inr (Or.inr (Or.inl (apply_mul_apply_eq_two_of_orderOf_eq_four hp hu hv hn)))

theorem eta_mem_of_orderOf_le_four [Module.Finite (ZMod p) U] (hp : p ≠ 2) {u v : U}
    {φ ψ : Module.Dual (ZMod p) U} (hu : φ u = 2) (hv : ψ v = 2)
    (h : orderOf (Module.reflection hu * Module.reflection hv) ≤ 4) :
    φ v * ψ u = 0 ∨ φ v * ψ u = 1 ∨ φ v * ψ u = 2 ∨ φ v * ψ u = 4 := by
  rcases eta_cases_of_orderOf_le_four hp hu hv h with ⟨h0, -⟩ | h | h | ⟨-, h⟩
  · exact Or.inl (by rw [h0, zero_mul])
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem orderOf_reflection_mul_eq_two (hp : p ≠ 2) {u v : U} {φ ψ : Module.Dual (ZMod p) U}
    (hu : φ u = 2) (hv : ψ v = 2) (h1 : φ v = 0) (h2 : ψ u = 0) :
    orderOf (Module.reflection hu * Module.reflection hv) = 2 := by
  refine orderOf_eq_prime (reflection_mul_reflection_pow_two hu hv h1 h2) ?_
  intro h
  have heq : Module.reflection hu = Module.reflection hv := by
    rw [eq_inv_of_mul_eq_one_left h, Module.reflection_inv]
  have h4 := mul_eq_four_of_reflection_eq hu hv heq
  rw [h1, zero_mul] at h4
  have h22 : (2 : ZMod p) * 2 = 0 := by linear_combination -h4
  exact ZMod.prime_ne_zero p 2 hp (mul_self_eq_zero.mp h22)

theorem orderOf_reflection_mul_eq_three (hp3 : p ≠ 3) {u v : U} {φ ψ : Module.Dual (ZMod p) U}
    (hu : φ u = 2) (hv : ψ v = 2) (h : φ v * ψ u = 1) :
    orderOf (Module.reflection hu * Module.reflection hv) = 3 := by
  refine orderOf_eq_prime (reflection_mul_reflection_pow_three hu hv h) ?_
  intro h1
  have heq : Module.reflection hu = Module.reflection hv := by
    rw [eq_inv_of_mul_eq_one_left h1, Module.reflection_inv]
  have h4 := mul_eq_four_of_reflection_eq hu hv heq
  rw [h] at h4
  have h3 : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -h4
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h3)

theorem orderOf_reflection_mul_eq_four (hp : p ≠ 2) {u v : U} {φ ψ : Module.Dual (ZMod p) U}
    (hu : φ u = 2) (hv : ψ v = 2) (h : φ v * ψ u = 2) :
    orderOf (Module.reflection hu * Module.reflection hv) = 4 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hsq : ¬ (Module.reflection hu * Module.reflection hv) ^ 2 ^ 1 = 1 := by
    intro hsq
    have hdvd : orderOf (Module.reflection hu * Module.reflection hv) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa using hsq)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
    · have heq : Module.reflection hu = Module.reflection hv := by
        rw [eq_inv_of_mul_eq_one_left (orderOf_eq_one_iff.mp h1), Module.reflection_inv]
      have h4 := mul_eq_four_of_reflection_eq hu hv heq
      rw [h] at h4
      exact h2 (by linear_combination -h4)
    · obtain ⟨h0, -⟩ := apply_eq_zero_of_orderOf_eq_two hp hu hv h2'
      rw [h0, zero_mul] at h
      exact h2 h.symm
  have h4 := reflection_mul_reflection_pow_four hu hv h
  exact orderOf_eq_prime_pow hsq (by simpa using h4)

theorem ne_of_root_quadratic {q : ℕ} {x : ZMod p} (a b : ℤ)
    (h : x ^ 2 + (a : ZMod p) * x + (b : ZMod p) = 0)
    (hq : ∀ y : ZMod q, y ^ 2 + (a : ZMod q) * y + (b : ZMod q) ≠ 0) : p ≠ q := by
  rintro rfl
  exact hq x h

section GammaP

variable [Module.Finite (ZMod p) U] {a b c : U ≃ₗ[ZMod p] U} {Γ : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem commutatorSpace_closure_le_span {n : ℕ} (g : Fin n → U ≃ₗ[ZMod p] U)
    (u : Fin n → U)
    (h : ∀ i, HardMathSupport.Kantor79.movedSpace (g i) ≤
      Submodule.span (ZMod p) (Set.range u)) :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range g)) ≤
      Submodule.span (ZMod p) (Set.range u) := by
  rw [HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace]
  exact iSup_le h

omit [Module.Finite (ZMod p) U] in
private theorem movedSpace_reflection_le_span_root {v : U} {φ : Module.Dual (ZMod p) U}
    (hφ : φ v = 2) :
    HardMathSupport.Kantor79.movedSpace (Module.reflection hφ) ≤
      Submodule.span (ZMod p) {v} := by
  rintro w ⟨x, rfl⟩
  change Module.reflection hφ x - x ∈ Submodule.span (ZMod p) {v}
  rw [Module.reflection_apply]
  rw [show x - φ x • v - x = -(φ x • v) by abel]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))

private theorem gammaP_commutatorSpace_le_span {v : Fin 3 → U}
    {φ : Fin 3 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (v i) = 2) :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure
      (Set.range fun i => Module.reflection (hφ i))) ≤
      Submodule.span (ZMod p) (Set.range v) := by
  refine commutatorSpace_closure_le_span _ v ?_
  intro i
  exact (movedSpace_reflection_le_span_root (hφ i)).trans
    (Submodule.span_mono (by rintro _ rfl; exact Set.mem_range_self i))

omit [Module.Finite (ZMod p) U] in
private theorem gammaP_scale_facts (hp : p ≠ 2) {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U}
    (hprodab : φa vb * φb va = 2) (hprodbc : φb vc * φc vb = 2) :
    ∃ (l1 l2 : ZMod p), l1 ≠ 0 ∧ l2 ≠ 0 ∧ φc vb = 2 * (φb vc)⁻¹ ∧
      φb va = 2 * (φa vb)⁻¹ ∧ φa vb ≠ 0 ∧ φb vc ≠ 0 ∧ (2 : ZMod p) ≠ 0 ∧
      φa vb * φb vc ≠ 0 ∧ l1 = -(φa vb)⁻¹ ∧ l2 = 2 * (φa vb * φb vc)⁻¹ ∧
      l1⁻¹ = -(φa vb) ∧ l2⁻¹ = (φa vb * φb vc) * (2 : ZMod p)⁻¹ := by
  have hφavb : φa vb ≠ 0 := fun h0 =>
    ZMod.prime_ne_zero p 2 hp (by
      have h := hprodab
      rw [h0, zero_mul] at h
      exact h.symm)
  have hφbvc : φb vc ≠ 0 := fun h0 =>
    ZMod.prime_ne_zero p 2 hp (by
      have h := hprodbc
      rw [h0, zero_mul] at h
      exact h.symm)
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hprodne : φa vb * φb vc ≠ 0 := mul_ne_zero hφavb hφbvc
  have hφcvb : φc vb = 2 * (φb vc)⁻¹ := by
    field_simp
    linear_combination hprodbc
  have hφbva : φb va = 2 * (φa vb)⁻¹ := by
    rw [← hprodab]
    field_simp
  refine ⟨-(φa vb)⁻¹, 2 * (φa vb * φb vc)⁻¹, ?_, ?_, hφcvb, hφbva, hφavb, hφbvc, h2ne,
    hprodne, rfl, rfl, ?_, ?_⟩
  · exact neg_ne_zero.mpr (inv_ne_zero hφavb)
  · exact mul_ne_zero h2ne (inv_ne_zero hprodne)
  · field_simp
  · rw [mul_inv_rev, inv_inv]

omit [Module.Finite (ZMod p) U] in
private theorem gammaP_rescaled_self {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U} {l1 l2 : ZMod p}
    (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2) (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) :
    ∀ i, (![φa, l1⁻¹ • φb, l2⁻¹ • φc] : Fin 3 → Module.Dual (ZMod p) U) i
      (![va, l1 • vb, l2 • vc] i) = 2 := by
  intro i
  fin_cases i
  · change φa va = 2
    exact hφa
  · change (l1⁻¹ • φb) (l1 • vb) = 2
    rw [LinearMap.smul_apply, smul_eq_mul, map_smul, smul_eq_mul, hφb, ← mul_assoc,
      inv_mul_cancel₀ hl1, one_mul]
  · change (l2⁻¹ • φc) (l2 • vc) = 2
    rw [LinearMap.smul_apply, smul_eq_mul, map_smul, smul_eq_mul, hφc, ← mul_assoc,
      inv_mul_cancel₀ hl2, one_mul]

private theorem gammaP_hle_roots {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U}
    {l1 l2 : ZMod p} (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure
      (Set.range ![Module.reflection hφa, Module.reflection hφb, Module.reflection hφc])) ≤
      Submodule.span (ZMod p) (Set.range ![va, l1 • vb, l2 • vc]) := by
  let w : Fin 3 → U := ![va, l1 • vb, l2 • vc]
  change HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure
      (Set.range ![Module.reflection hφa, Module.reflection hφb, Module.reflection hφc])) ≤
      Submodule.span (ZMod p) (Set.range w)
  have hvb : vb = l1⁻¹ • w 1 := by
    change vb = l1⁻¹ • (l1 • vb)
    rw [smul_smul, inv_mul_cancel₀ hl1, one_smul]
  have hvc : vc = l2⁻¹ • w 2 := by
    change vc = l2⁻¹ • (l2 • vc)
    rw [smul_smul, inv_mul_cancel₀ hl2, one_smul]
  have hspan0 : Submodule.span (ZMod p) {va} ≤ Submodule.span (ZMod p) (Set.range w) :=
    Submodule.span_mono (by
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨0, rfl⟩)
  have hspan1 : Submodule.span (ZMod p) {vb} ≤ Submodule.span (ZMod p) (Set.range w) := by
    rw [Submodule.span_le]
    rintro _ rfl
    rw [hvb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (1 : Fin 3)))
  have hspan2 : Submodule.span (ZMod p) {vc} ≤ Submodule.span (ZMod p) (Set.range w) := by
    rw [Submodule.span_le]
    rintro _ rfl
    rw [hvc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (2 : Fin 3)))
  refine commutatorSpace_closure_le_span _ w ?_
  intro i
  fin_cases i
  · exact (movedSpace_reflection_le_span_root hφa).trans hspan0
  · exact (movedSpace_reflection_le_span_root hφb).trans hspan1
  · exact (movedSpace_reflection_le_span_root hφc).trans hspan2

omit [Module.Finite (ZMod p) U] in
private theorem gammaP_final_refl {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U}
    {l1 l2 : ZMod p} (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0)
    (hφ : ∀ i, (![φa, l1⁻¹ • φb, l2⁻¹ • φc] : Fin 3 → Module.Dual (ZMod p) U) i
      (![va, l1 • vb, l2 • vc] i) = 2) :
    Module.reflection hφa = Module.reflection (hφ 0) ∧
    Module.reflection hφb = Module.reflection (hφ 1) ∧
    Module.reflection hφc = Module.reflection (hφ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · ext w
    rw [show Module.reflection hφa w = w - φa w • va from Module.reflection_apply w hφa,
      show Module.reflection (hφ 0) w = w - (![φa, l1⁻¹ • φb, l2⁻¹ • φc]) 0 w •
        (![va, l1 • vb, l2 • vc]) 0 from Module.reflection_apply w (hφ 0)]
    rfl
  · ext w
    rw [show Module.reflection hφb w = w - φb w • vb from Module.reflection_apply w hφb,
      show Module.reflection (hφ 1) w = w - (![φa, l1⁻¹ • φb, l2⁻¹ • φc]) 1 w •
        (![va, l1 • vb, l2 • vc]) 1 from Module.reflection_apply w (hφ 1)]
    change w - φb w • vb = w - (l1⁻¹ • φb) w • (l1 • vb)
    rw [LinearMap.smul_apply, smul_eq_mul, smul_smul,
      show l1⁻¹ * φb w * l1 = φb w by
        rw [mul_comm (l1⁻¹) (φb w), mul_assoc, inv_mul_cancel₀ hl1, mul_one]]
  · ext w
    rw [show Module.reflection hφc w = w - φc w • vc from Module.reflection_apply w hφc,
      show Module.reflection (hφ 2) w = w - (![φa, l1⁻¹ • φb, l2⁻¹ • φc]) 2 w •
        (![va, l1 • vb, l2 • vc]) 2 from Module.reflection_apply w (hφ 2)]
    change w - φc w • vc = w - (l2⁻¹ • φc) w • (l2 • vc)
    rw [LinearMap.smul_apply, smul_eq_mul, smul_smul,
      show l2⁻¹ * φc w * l2 = φc w by
        rw [mul_comm (l2⁻¹) (φc w), mul_assoc, inv_mul_cancel₀ hl2, mul_one]]

omit [Module.Finite (ZMod p) U] in
private theorem gammaP_final_pair {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U}
    {l1 l2 : ZMod p} (hφavb : φa vb ≠ 0) (hφbvc : φb vc ≠ 0) (h2ne : (2 : ZMod p) ≠ 0)
    (hφavc : φa vc = 0) (hφcva : φc va = 0)
    (hl1val : l1 = -(φa vb)⁻¹) (hl2val : l2 = 2 * (φa vb * φb vc)⁻¹)
    (hl1inv : l1⁻¹ = -(φa vb)) (hl2inv : l2⁻¹ = (φa vb * φb vc) * (2 : ZMod p)⁻¹)
    (hφcvb : φc vb = 2 * (φb vc)⁻¹) (hφbva : φb va = 2 * (φa vb)⁻¹) :
    (![φa, l1⁻¹ • φb, l2⁻¹ • φc] : Fin 3 → Module.Dual (ZMod p) U) 0
        ((![va, l1 • vb, l2 • vc]) 1) = -1 ∧
    (![φa, l1⁻¹ • φb, l2⁻¹ • φc] : Fin 3 → Module.Dual (ZMod p) U) 1
        ((![va, l1 • vb, l2 • vc]) 0) = -2 ∧
    (![φa, l1⁻¹ • φb, l2⁻¹ • φc] : Fin 3 → Module.Dual (ZMod p) U) 1
        ((![va, l1 • vb, l2 • vc]) 2) = -2 ∧
    (![φa, l1⁻¹ • φb, l2⁻¹ • φc] : Fin 3 → Module.Dual (ZMod p) U) 2
        ((![va, l1 • vb, l2 • vc]) 1) = -1 ∧
    (![φa, l1⁻¹ • φb, l2⁻¹ • φc] : Fin 3 → Module.Dual (ZMod p) U) 0
        ((![va, l1 • vb, l2 • vc]) 2) = 0 ∧
    (![φa, l1⁻¹ • φb, l2⁻¹ • φc] : Fin 3 → Module.Dual (ZMod p) U) 2
        ((![va, l1 • vb, l2 • vc]) 0) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change φa (l1 • vb) = -1
    rw [map_smul, smul_eq_mul, hl1val]
    field_simp [hφavb]
  · change (l1⁻¹ • φb) va = -2
    rw [LinearMap.smul_apply, smul_eq_mul, hl1inv, hφbva]
    field_simp [hφavb]
  · change (l1⁻¹ • φb) (l2 • vc) = -2
    rw [LinearMap.smul_apply, map_smul, smul_smul, smul_eq_mul, hl1inv, hl2val]
    field_simp [hφavb, hφbvc]
  · change (l2⁻¹ • φc) (l1 • vb) = -1
    rw [LinearMap.smul_apply, map_smul, smul_smul, smul_eq_mul, hl2inv, hl1val, hφcvb]
    field_simp [hφavb, hφbvc, h2ne]
  · change φa (l2 • vc) = 0
    rw [map_smul, smul_eq_mul, hφavc, mul_zero]
  · change (l2⁻¹ • φc) va = 0
    rw [LinearMap.smul_apply, smul_eq_mul, hφcva, mul_zero]

theorem exists_rootMatrix_gammaP (hp : p ≠ 2) (ha : IsRefl p a) (hb : IsRefl p b)
    (hc : IsRefl p c) (hab : orderOf (a * b) = 4) (hbc : orderOf (b * c) = 4)
    (hac : orderOf (a * c) = 2) (hΓ : Γ = Subgroup.closure {a, b, c})
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Γ) = 3) :
    ∃ (v : Fin 3 → U) (φ : Fin 3 → Module.Dual (ZMod p) U) (hφ : ∀ i, φ i (v i) = 2),
      LinearIndependent (ZMod p) v ∧ a = Module.reflection (hφ 0) ∧
      b = Module.reflection (hφ 1) ∧ c = Module.reflection (hφ 2) ∧
      φ 0 (v 1) = -1 ∧ φ 1 (v 0) = -2 ∧ φ 1 (v 2) = -2 ∧ φ 2 (v 1) = -1 ∧
      φ 0 (v 2) = 0 ∧ φ 2 (v 0) = 0 := by
  obtain ⟨va, φa, hφa, rfl⟩ := (isRefl_iff hp a).mp ha
  obtain ⟨vb, φb, hφb, rfl⟩ := (isRefl_iff hp b).mp hb
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp hc
  obtain ⟨hφavc, hφcva⟩ := apply_eq_zero_of_orderOf_eq_two hp hφa hφc hac
  have hprodab := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb hab
  have hprodbc := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφb hφc hbc
  obtain ⟨l1, l2, hl1, hl2, hφcvb, hφbva, hφavb, hφbvc, h2ne, hprodne, hl1val, hl2val,
    hl1inv, hl2inv⟩ := gammaP_scale_facts hp hprodab hprodbc
  have hφ : ∀ i, (![φa, l1⁻¹ • φb, l2⁻¹ • φc] : Fin 3 → Module.Dual (ZMod p) U) i
      (![va, l1 • vb, l2 • vc] i) = 2 := gammaP_rescaled_self hφa hφb hφc hl1 hl2
  have hΓrange : Γ = Subgroup.closure
      (Set.range ![Module.reflection hφa, Module.reflection hφb, Module.reflection hφc]) := by
    rw [hΓ]; congr 1; ext x; simp
    tauto
  have hle : HardMathSupport.Kantor79.commutatorSpace Γ ≤
      Submodule.span (ZMod p) (Set.range ![va, l1 • vb, l2 • vc]) := by
    rw [hΓrange]
    exact gammaP_hle_roots hφa hφb hφc hl1 hl2
  have hge : 3 ≤ Module.finrank (ZMod p)
      (Submodule.span (ZMod p) (Set.range ![va, l1 • vb, l2 • vc])) := by
    have h := Submodule.finrank_mono hle
    rwa [hdim] at h
  have hind : LinearIndependent (ZMod p) ![va, l1 • vb, l2 • vc] := by
    rw [linearIndependent_iff_card_le_finrank_span, Fintype.card_fin]
    exact hge
  obtain ⟨haeq, hbeq, hceq⟩ := gammaP_final_refl hφa hφb hφc hl1 hl2 hφ
  obtain ⟨h01, h10, h12, h21, h02, h20⟩ :=
    gammaP_final_pair hφavb hφbvc h2ne hφavc hφcva hl1val hl2val hl1inv hl2inv
      hφcvb hφbva
  exact ⟨![va, l1 • vb, l2 • vc], ![φa, l1⁻¹ • φb, l2⁻¹ • φc], hφ, hind, haeq, hbeq, hceq,
    h01, h10, h12, h21, h02, h20⟩

omit [Module.Finite (ZMod p) U] in
private theorem gammaP_babc_action {v : Fin 3 → U} {φ : Fin 3 → Module.Dual (ZMod p) U}
    (hφ : ∀ i, φ i (v i) = 2) (h01 : φ 0 (v 1) = -1) (h02 : φ 0 (v 2) = 0)
    (h10 : φ 1 (v 0) = -2) (h12 : φ 1 (v 2) = -2) (h20 : φ 2 (v 0) = 0)
    (h21 : φ 2 (v 1) = -1) :
    (Module.reflection (hφ 1) * Module.reflection (hφ 0) * Module.reflection (hφ 1) *
        Module.reflection (hφ 2)) (v 0) = v 0 ∧
    (Module.reflection (hφ 1) * Module.reflection (hφ 0) * Module.reflection (hφ 1) *
        Module.reflection (hφ 2)) (v 1) = v 0 + 3 • v 1 + v 2 ∧
    (Module.reflection (hφ 1) * Module.reflection (hφ 0) * Module.reflection (hφ 1) *
        Module.reflection (hφ 2)) (v 2) = -2 • v 0 - 4 • v 1 - v 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · (simp only [LinearEquiv.mul_apply, Module.reflection_apply, map_sub, map_smul,
        hφ 0, hφ 1, hφ 2, h01, h02, h10, h12, h20, h21]; module)

omit [Module.Finite (ZMod p) U] in
private theorem orderOf_eq_prime_of_sub_eq {g : U ≃ₗ[ZMod p] U} {n : Module.End (ZMod p) U}
    (hp : p ≠ 2) (hu : ∃ u : U, u ≠ 0) (hg : (g : U →ₗ[ZMod p] U) = 1 + n)
    (hn3 : n ^ 3 = 0) (hgne : g ≠ 1) : orderOf g = p := by
  obtain ⟨u0, hu0⟩ := hu
  have hinj : Function.Injective (algebraMap (ZMod p) (Module.End (ZMod p) U)) := by
    intro c d hcd
    have h : c • (1 : Module.End (ZMod p) U) = d • (1 : Module.End (ZMod p) U) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hcd
    have h2 : ((c - d) • (1 : Module.End (ZMod p) U)) = 0 := by rw [sub_smul, h, sub_self]
    have h3 : (c - d) • u0 = 0 := by
      have := congrArg (fun (f : Module.End (ZMod p) U) => f u0) h2
      simpa using this
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hu0)
  have hchar : CharP (Module.End (ZMod p) U) p := charP_of_injective_algebraMap hinj p
  have hgnpow : (g : U →ₗ[ZMod p] U) ^ p = 1 := by
    rw [hg, add_pow_char_of_commute p (Commute.one_left n), one_pow]
    have hnp : n ^ p = 0 := by
      have hp3 : 3 ≤ p := by
        have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
        omega
      exact pow_eq_zero_of_le hp3 hn3
    rw [hnp, add_zero]
  have hcoe : ((g ^ p : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      (g : U →ₗ[ZMod p] U) ^ p := by
    simpa using map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) g p
  have hgpow : g ^ p = 1 := by
    apply LinearEquiv.ext
    intro x
    have h := congrArg (fun (L : U →ₗ[ZMod p] U) => L x) hgnpow
    rw [← hcoe] at h
    simpa using h
  exact orderOf_eq_prime hgpow hgne

omit [Module.Finite (ZMod p) U] in
private theorem gammaP_babc_nfacts {v : Fin 3 → U} {φ : Fin 3 → Module.Dual (ZMod p) U}
    {g : U ≃ₗ[ZMod p] U} (hφ : ∀ i, φ i (v i) = 2)
    (hg_eq : g = Module.reflection (hφ 1) * Module.reflection (hφ 0) *
      Module.reflection (hφ 1) * Module.reflection (hφ 2))
    (hind : LinearIndependent (ZMod p) v)
    (h01 : φ 0 (v 1) = -1) (h02 : φ 0 (v 2) = 0) (h10 : φ 1 (v 0) = -2)
    (h12 : φ 1 (v 2) = -2) (h20 : φ 2 (v 0) = 0) (h21 : φ 2 (v 1) = -1) :
    ∃ (z : U) (n : Module.End (ZMod p) U),
      z = v 0 + (2 : ZMod p) • v 1 + v 2 ∧ n = (g : U →ₗ[ZMod p] U) - 1 ∧
      z ≠ 0 ∧ n (v 0) = 0 ∧ n (v 1) = z ∧ n (v 2) = (-2 : ZMod p) • z ∧ n z = 0 ∧
      (∀ i, n (v i) ∈ Submodule.span (ZMod p) ({z} : Set U)) := by
  obtain ⟨hgv0, hgv1, hgv2⟩ := gammaP_babc_action hφ h01 h02 h10 h12 h20 h21
  have hgv0' : g (v 0) = v 0 := by rw [hg_eq]; exact hgv0
  have hgv1' : g (v 1) = v 0 + 3 • v 1 + v 2 := by rw [hg_eq]; exact hgv1
  have hgv2' : g (v 2) = -2 • v 0 - 4 • v 1 - v 2 := by rw [hg_eq]; exact hgv2
  have hz_ne : v 0 + (2 : ZMod p) • v 1 + v 2 ≠ 0 := by
    intro hz
    have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 3)),
        (![1, 2, 1] : Fin 3 → ZMod p) i • v i = 0 := by
      simpa [Fin.sum_univ_three] using hz
    have h0 := (linearIndependent_iff'.mp hind) (Finset.univ : Finset (Fin 3))
      (![1, 2, 1] : Fin 3 → ZMod p) hsum 0 (Finset.mem_univ 0)
    norm_num at h0
  have hn0 : ((g : U →ₗ[ZMod p] U) - 1) (v 0) = 0 := by
    change g (v 0) - v 0 = 0
    rw [hgv0', sub_self]
  have hn1 : ((g : U →ₗ[ZMod p] U) - 1) (v 1) = v 0 + (2 : ZMod p) • v 1 + v 2 := by
    change g (v 1) - v 1 = v 0 + (2 : ZMod p) • v 1 + v 2
    rw [hgv1']; module
  have hn2 : ((g : U →ₗ[ZMod p] U) - 1) (v 2) =
      (-2 : ZMod p) • (v 0 + (2 : ZMod p) • v 1 + v 2) := by
    change g (v 2) - v 2 = (-2 : ZMod p) • (v 0 + (2 : ZMod p) • v 1 + v 2)
    rw [hgv2']; module
  have hnz : ((g : U →ₗ[ZMod p] U) - 1) (v 0 + (2 : ZMod p) • v 1 + v 2) = 0 := by
    rw [map_add, map_add, map_smul, hn0, hn1, hn2]
    module
  refine ⟨v 0 + (2 : ZMod p) • v 1 + v 2, (g : U →ₗ[ZMod p] U) - 1, rfl, rfl, hz_ne,
    hn0, hn1, hn2, hnz, ?_⟩
  intro i
  fin_cases i
  · simp [hn0]
  · simp [hn1]
  · simpa [hn2] using Submodule.smul_mem (p := Submodule.span (ZMod p)
      ({v 0 + (2 : ZMod p) • v 1 + v 2} : Set U)) (-2 : ZMod p)
      (Submodule.subset_span (Set.mem_singleton _))

private theorem gammaP_gamma_range_le {v : Fin 3 → U} {φ : Fin 3 → Module.Dual (ZMod p) U}
    {a b c : U ≃ₗ[ZMod p] U} (hΓ : Γ = Subgroup.closure {a, b, c}) (hφ : ∀ i, φ i (v i) = 2)
    (ha_eq : a = Module.reflection (hφ 0)) (hb_eq : b = Module.reflection (hφ 1))
    (hc_eq : c = Module.reflection (hφ 2)) :
    HardMathSupport.Kantor79.commutatorSpace Γ ≤ Submodule.span (ZMod p) (Set.range v) := by
  have hΓrange : Γ = Subgroup.closure (Set.range fun i => Module.reflection (hφ i)) := by
    rw [hΓ, ha_eq, hb_eq, hc_eq]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  rw [hΓrange]
  exact gammaP_commutatorSpace_le_span hφ

omit [Module.Finite (ZMod p) U] in
private theorem gammaP_n_pow_three {v : Fin 3 → U} {z : U} {V : Submodule (ZMod p) U}
    {n : Module.End (ZMod p) U}
    (hnV : ∀ u, n u ∈ V) (hVle : V ≤ Submodule.span (ZMod p) (Set.range v))
    (hnvi : ∀ i, n (v i) ∈ Submodule.span (ZMod p) ({z} : Set U)) (hnz : n z = 0) :
    n ^ 3 = 0 := by
  ext u
  change n (n (n u)) = 0
  have h2 : n (n u) ∈ Submodule.span (ZMod p) ({z} : Set U) := by
    have hw : n u ∈ Submodule.span (ZMod p) (Set.range v) := hVle (hnV u)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hw
    rw [← hc, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hnvi i)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h2
  rw [← hc, map_smul, hnz, smul_zero]

theorem orderOf_babc_gammaP (hp : p ≠ 2) (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c)
    (hab : orderOf (a * b) = 4) (hbc : orderOf (b * c) = 4) (hac : orderOf (a * c) = 2)
    (hΓ : Γ = Subgroup.closure {a, b, c})
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Γ) = 3) :
    orderOf (b * a * b * c) = p := by
  obtain ⟨v, φ, hφ, hind, ha_eq, hb_eq, hc_eq, h01, h10, h12, h21, h02, h20⟩ :=
    exists_rootMatrix_gammaP hp ha hb hc hab hbc hac hΓ hdim
  set g : U ≃ₗ[ZMod p] U := b * a * b * c with hg_def
  have hg_eq : g = Module.reflection (hφ 1) * Module.reflection (hφ 0) *
      Module.reflection (hφ 1) * Module.reflection (hφ 2) := by
    rw [hg_def, ha_eq, hb_eq, hc_eq]
  obtain ⟨z, n, -, hn_def, hz_ne, hn0, hn1, hn2, hnz, hnvi⟩ :=
    gammaP_babc_nfacts hφ hg_eq hind h01 h02 h10 h12 h20 h21
  have hgmem : g ∈ Γ := by
    rw [hg_def, hΓ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  have hnV : ∀ u, n u ∈ HardMathSupport.Kantor79.commutatorSpace Γ := by
    intro u
    have h := (commutatorSpace_le_iff (H := Γ)
      (W := HardMathSupport.Kantor79.commutatorSpace Γ)).mp le_rfl g hgmem u
    rw [hn_def]
    simpa [LinearMap.sub_apply] using h
  have hVle := gammaP_gamma_range_le (Γ := Γ) (v := v) hΓ hφ ha_eq hb_eq hc_eq
  have hn3 : n ^ 3 = 0 := gammaP_n_pow_three hnV hVle hnvi hnz
  have hgne : g ≠ 1 := by
    intro h
    apply hz_ne
    have hnzero : n = 0 := by
      rw [hn_def, h]
      ext u
      simp
    have := congrArg (fun (m : Module.End (ZMod p) U) => m (v 1)) hnzero
    rw [hn1] at this
    simpa using this
  have hv0 : v 0 ≠ 0 := by
    intro h0
    exact (ZMod.prime_ne_zero p 2 hp) ((hφ 0).symm.trans (by rw [h0, map_zero]))
  exact orderOf_eq_prime_of_sub_eq hp ⟨v 0, hv0⟩ (by rw [hn_def]; abel) hn3 hgne

private theorem isRefl_conj_of_isRefl (hp : p ≠ 2) {t g : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) :
    IsRefl p (g * t * g⁻¹) := by
  obtain ⟨v, φ, hφ, rfl⟩ := (isRefl_iff hp t).mp ht
  have hφ' : (φ.comp (g.symm : U →ₗ[ZMod p] U)) (g v) = 2 := by
    simp [LinearMap.comp_apply, hφ]
  refine (isRefl_iff hp _).mpr ⟨g v, φ.comp (g.symm : U →ₗ[ZMod p] U), hφ', ?_⟩
  ext x
  simp [LinearEquiv.mul_apply, Module.reflection_apply, LinearMap.comp_apply]

theorem exists_orderOf_mul_eq_max_gammaP (hp : p ≠ 2) (ha : IsRefl p a) (hb : IsRefl p b)
    (hc : IsRefl p c) (hab : orderOf (a * b) = 4) (hbc : orderOf (b * c) = 4)
    (hac : orderOf (a * c) = 2) (hΓ : Γ = Subgroup.closure {a, b, c})
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Γ) = 3) :
    ∃ x ∈ Γ, ∃ y ∈ Γ, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = max 4 p := by
  by_cases hp3 : p = 3
  · have hmax : max 4 p = 4 := by omega
    exact ⟨a, by rw [hΓ]; exact Subgroup.subset_closure (by simp), b,
      by rw [hΓ]; exact Subgroup.subset_closure (by simp), ha, hb, by rw [hmax]; exact hab⟩
  · have hmax : max 4 p = p := by
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      omega
    have hbab_refl : IsRefl p (b * a * b) := by
      have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb.1
      simpa [hb_inv] using isRefl_conj_of_isRefl (g := b) hp ha
    refine ⟨b * a * b, ?_, c, by rw [hΓ]; exact Subgroup.subset_closure (by simp), hbab_refl,
      hc, by rw [hmax]; exact orderOf_babc_gammaP hp ha hb hc hab hbc hac hΓ hdim⟩
    rw [hΓ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))

end GammaP

theorem exists_starGauge {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U}
    (hφb : φb vb = 2) (hφc : φc vc = 2) (hac : φa vc ≠ 0) (hcb : φc vb ≠ 0) :
    ∃ (vb' vc' : U) (φb' φc' : Module.Dual (ZMod p) U) (hb' : φb' vb' = 2) (hc' : φc' vc' = 2),
      Module.reflection hb' = Module.reflection hφb ∧
      Module.reflection hc' = Module.reflection hφc ∧
      φa vc' = -1 ∧ φc' vb' = -1 ∧ φc' va = -(φa vc * φc va) ∧ φb' vc' = -(φb vc * φc vb) ∧
      φb' va = φa vc * φc vb * φb va ∧
      φa vb' * (φa vc * φc va) * (φb vc * φc vb) = φa vb * φb vc * φc va ∧
      (∃ l : ZMod p, l ≠ 0 ∧ vb' = l • vb) ∧ ∃ l : ZMod p, l ≠ 0 ∧ vc' = l • vc := by
  have ht : (φa vc * φc vb)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hac hcb)
  have hl : -(φa vc)⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hac)
  refine ⟨(φa vc * φc vb)⁻¹ • vb, (-(φa vc)⁻¹) • vc, ((φa vc * φc vb)⁻¹)⁻¹ • φb,
    (-(φa vc)⁻¹)⁻¹ • φc, smul_pairing hφb ht, smul_pairing hφc hl, reflection_smul hφb ht,
    reflection_smul hφc hl, ?_, ?_, ?_, ?_, ?_, ?_, ⟨_, ht, rfl⟩, ⟨_, hl, rfl⟩⟩ <;>
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] <;> field_simp

theorem range_fin_three {α : Type*} (x : Fin 3 → α) : Set.range x = {x 0, x 1, x 2} := by
  ext y
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem splitSupport_closure_three [Module.Finite (ZMod p) U] {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (hab : φa vb * φb va ≠ 0) (hac : φa vc * φc va ≠ 0) (hbc : φb vc * φc vb ≠ 0)
    (hdet : 8 - 2 * (φa vb * φb va + φa vc * φc va + φb vc * φc vb) +
      (φa vb * φb vc * φc va + φa vc * φc vb * φb va) ≠ 0) :
    SplitSupport (Subgroup.closure ({Module.reflection hφa, Module.reflection hφb,
      Module.reflection hφc} : Set (U ≃ₗ[ZMod p] U))) 3 := by
  let u : Fin 3 → U := ![va, vb, vc]
  let φ : Fin 3 → Module.Dual (ZMod p) U := ![φa, φb, φc]
  have hφ : ∀ i, φ i (u i) = 2 := by intro i; fin_cases i <;> simp [u, φ, hφa, hφb, hφc]
  have hd : (Matrix.of fun i j => φ i (u j)).det ≠ 0 := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, u, φ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hφa, hφb, hφc]
    convert hdet using 1
    ring
  have hne : ∀ i j, i ≠ j → φ j (u i) ≠ 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [u, φ] at hij ⊢ <;> simp at hij ⊢
    · exact right_ne_zero_of_mul hab
    · exact right_ne_zero_of_mul hac
    · exact left_ne_zero_of_mul hab
    · exact right_ne_zero_of_mul hbc
    · exact left_ne_zero_of_mul hac
    · exact left_ne_zero_of_mul hbc
  have hconn : ∀ I : Finset (Fin 3), I.Nonempty → I ≠ Finset.univ →
      ∃ i ∈ I, ∃ j ∉ I, φ j (u i) ≠ 0 := by
    intro I ⟨i, hi⟩ hI
    obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
      by_contra h
      push Not at h
      exact hI (Finset.eq_univ_of_forall h)
    exact ⟨i, hi, j, hj, hne i j (by rintro rfl; exact hj hi)⟩
  have hss := splitSupport_of_det_ne_zero hφ hd hconn
  rw [range_fin_three] at hss
  exact hss

theorem exists_basis_of_pairing [Module.Finite (ZMod p) U] {V : Submodule (ZMod p) U}
    (hV : Module.finrank (ZMod p) V = 3) {e : Fin 3 → U} (he : ∀ k, e k ∈ V)
    {ψ : Fin 3 → Module.Dual (ZMod p) U} (hdet : (Matrix.of fun i k => ψ i (e k)).det ≠ 0) :
    ∃ g : Module.Basis (Fin 3) (ZMod p) V, ∀ k, (g k : U) = e k := by
  let e' : Fin 3 → V := fun k => ⟨e k, he k⟩
  have hli : LinearIndependent (ZMod p) e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hrow : ∀ i, ψ i (e 0) * c 0 + ψ i (e 1) * c 1 + ψ i (e 2) * c 2 = 0 := by
      intro i
      have := congrArg (ψ i) hc
      simp only [Fin.sum_univ_three, map_add, map_smul, smul_eq_mul, map_zero] at this
      linear_combination this
    have h3 : (![c 0, c 1, c 2] : Fin 3 → ZMod p) = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero hdet
      ext i
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hrow i
    intro k
    fin_cases k
    · simpa using congrFun h3 0
    · simpa using congrFun h3 1
    · simpa using congrFun h3 2
  have hli' : LinearIndependent (ZMod p) e' := LinearIndependent.of_comp V.subtype hli
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli' (by rw [hV]; rfl), fun k => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]⟩

theorem restrictHom_eq_of_basis {H : Subgroup (U ≃ₗ[ZMod p] U)} {n : ℕ}
    (g : Module.Basis (Fin n) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H))
    {x : U ≃ₗ[ZMod p] U} (hx : x ∈ H)
    {y : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H}
    (h : ∀ k, x (g k) = (y (g k) : U)) :
    restrictHom H _ (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨x, hx⟩ = y := by
  refine LinearEquiv.toLinearMap_injective (g.ext fun k => Subtype.ext ?_)
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, restrictHom_apply]
  exact h k

theorem restrictHom_eq_of_basis3 {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (g : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H))
    {x : U ≃ₗ[ZMod p] U} (hx : x ∈ H)
    {y : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H}
    (h0 : x (g 0) = (y (g 0) : U)) (h1 : x (g 1) = (y (g 1) : U))
    (h2 : x (g 2) = (y (g 2) : U)) :
    restrictHom H _ (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨x, hx⟩ = y :=
  restrictHom_eq_of_basis g hx fun k => by fin_cases k; exacts [h0, h1, h2]

theorem restrictHom_mem_movedGroup {H : Subgroup (U ≃ₗ[ZMod p] U)} {x : U ≃ₗ[ZMod p] U}
    (hx : x ∈ H) :
    restrictHom H _ (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨x, hx⟩ ∈
      movedGroup H :=
  ⟨⟨x, hx⟩, rfl⟩

theorem movedGroup_closure_le {S : Set (U ≃ₗ[ZMod p] U)}
    {K : Subgroup (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure S) ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure S))}
    (hK : ∀ x (hx : x ∈ S), restrictHom (Subgroup.closure S) _
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨x, Subgroup.subset_closure hx⟩ ∈ K) :
    movedGroup (Subgroup.closure S) ≤ K := by
  change (restrictHom (Subgroup.closure S) _
    (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)).range ≤ K
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := S),
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨⟨x, hx'⟩, hx, rfl⟩
  exact hK x hx

theorem movedGroup_closure_eq {S : Set (U ≃ₗ[ZMod p] U)}
    {T : Set (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure S) ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure S))}
    (hS : ∀ x (hx : x ∈ S), restrictHom (Subgroup.closure S) _
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨x, Subgroup.subset_closure hx⟩ ∈
        Subgroup.closure T)
    (hT : T ⊆ movedGroup (Subgroup.closure S)) :
    movedGroup (Subgroup.closure S) = Subgroup.closure T :=
  le_antisymm (movedGroup_closure_le hS) ((Subgroup.closure_le _).mpr hT)

theorem permMap_mem_of_swap {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    {M : Subgroup (W ≃ₗ[ZMod p] W)} (g : Module.Basis (Fin 3) (ZMod p) W)
    (h01 : permMap p g (Equiv.swap 0 1) ∈ M) (h12 : permMap p g (Equiv.swap 1 2) ∈ M)
    (σ : Equiv.Perm (Fin 3)) : permMap p g σ ∈ M := by
  let φ : Equiv.Perm (Fin 3) →* (W ≃ₗ[ZMod p] W) :=
    { toFun := permMap p g
      map_one' := g.ext' fun k => by rw [permMap_apply_basis]; rfl
      map_mul' := fun σ τ => (permMap_mul g σ τ).symm }
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 2 =>
      Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  change φ σ ∈ M
  induction hσ using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · exact h01
    · exact h12
  | one => rw [map_one]; exact M.one_mem
  | mul x y _ _ hx hy => rw [map_mul]; exact M.mul_mem hx hy

theorem orderOf_unit_eq_four (hp : p ≠ 2) {ζ : (ZMod p)ˣ} (h : (ζ : ZMod p) ^ 2 = -1) :
    orderOf ζ = 4 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ¬ ζ ^ 2 ^ 1 = 1 := by
    intro h1
    have := congrArg Units.val h1
    rw [pow_one, Units.val_pow_eq_pow_val, h, Units.val_one] at this
    exact h2 (by linear_combination -this)
  have h4 : ζ ^ 2 ^ (1 + 1) = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h]
    norm_num
  simpa using orderOf_eq_prime_pow hne h4

private theorem pairing_433 {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U}
    (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2) {u : ZMod p} (hu : u ^ 2 = -1)
    (hab : φa vb = 1 + u) (hba : φb va = 1 - u) (hac : φa vc = -1) (hca : φc va = -1)
    (hbc : φb vc = -1) (hcb : φc vb = -1) :
    (φa ((u + 1) • (va - vb)) = 2 ∧ φa ((u - 1) • va - (u + 1) • vb) = -2 ∧
      φa ((u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc) = 0) ∧
    (φb ((u + 1) • (va - vb)) = -2 * u ∧ φb ((u - 1) • va - (u + 1) • vb) = -2 ∧
      φb ((u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc) = 0) ∧
    (φc ((u + 1) • (va - vb)) = 0 ∧ φc ((u - 1) • va - (u + 1) • vb) = 2 ∧
      φc ((u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc) = -2) := by
  simp only [map_sub, map_smul, smul_eq_mul, hφa, hφb, hφc, hab, hba, hac, hca, hbc, hcb]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · linear_combination -hu
  · linear_combination -hu
  · linear_combination -hu
  · linear_combination -hu
  · linear_combination -hu
  · linear_combination -hu
  · ring
  · ring
  · ring

private theorem action_433 {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U}
    (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2) {u : ZMod p} (hu : u ^ 2 = -1)
    (hab : φa vb = 1 + u) (hba : φb va = 1 - u) (hac : φa vc = -1) (hca : φc va = -1)
    (hbc : φb vc = -1) (hcb : φc vb = -1) :
    Module.reflection hφa ((u + 1) • (va - vb)) = (u - 1) • va - (u + 1) • vb ∧
    Module.reflection hφa ((u - 1) • va - (u + 1) • vb) = (u + 1) • (va - vb) ∧
    Module.reflection hφc ((u - 1) • va - (u + 1) • vb) =
      (u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc ∧
    Module.reflection hφc ((u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc) =
      (u - 1) • va - (u + 1) • vb ∧
    Module.reflection hφb ((u + 1) • (va - vb)) = (-u) • ((u - 1) • va - (u + 1) • vb) ∧
    Module.reflection hφb ((u - 1) • va - (u + 1) • vb) = u • ((u + 1) • (va - vb)) ∧
    Module.reflection hφa ((u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc) =
      (u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc ∧
    Module.reflection hφc ((u + 1) • (va - vb)) = (u + 1) • (va - vb) ∧
    Module.reflection hφb ((u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc) =
      (u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc := by
  obtain ⟨⟨pa0, pa1, pa2⟩, ⟨pb0, pb1, pb2⟩, ⟨pc0, pc1, pc2⟩⟩ :=
    pairing_433 hφa hφb hφc hu hab hba hac hca hbc hcb
  simp only [Module.reflection_apply, pa0, pa1, pa2, pb0, pb1, pb2, pc0, pc1, pc2, zero_smul,
    sub_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial, trivial, trivial⟩
  · module
  · module
  · trivial
  · module
  · linear_combination (norm := module) hu • va - hu • vb
  · linear_combination (norm := module) (-hu) • va + hu • vb

private theorem det_433 (hp : p ≠ 2) {u : ZMod p} (hu : u ^ 2 = -1) :
    (!![2, -2, 0; -2 * u, -2, 0; 0, 2, -2] : Matrix (Fin 3) (Fin 3) (ZMod p)).det ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const]
  intro h
  have hu1 : u + 1 = 0 := by
    have : (8 : ZMod p) * (u + 1) = 0 := by linear_combination h
    have h8 : (8 : ZMod p) ≠ 0 := by
      have : (8 : ZMod p) = 2 * 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h2
    exact (mul_eq_zero.mp this).resolve_left h8
  apply h2
  linear_combination (1 - u) * hu1 + hu

theorem movedGroup_eq_gmmn {x y z : U ≃ₗ[ZMod p] U}
    (g : Module.Basis (Fin 3) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {x, y, z})))
    (ζ : (ZMod p)ˣ)
    (hx : restrictHom (Subgroup.closure {x, y, z}) _
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
      ⟨x, Subgroup.subset_closure (by simp)⟩ = permMap p g (Equiv.swap 0 1))
    (hy : restrictHom (Subgroup.closure {x, y, z}) _
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
      ⟨y, Subgroup.subset_closure (by simp)⟩ =
        permMap p g (Equiv.swap 0 1) * diagMap p g (pairUnit p 0 1 ζ))
    (hz : restrictHom (Subgroup.closure {x, y, z}) _
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
      ⟨z, Subgroup.subset_closure (by simp)⟩ = permMap p g (Equiv.swap 1 2)) :
    movedGroup (Subgroup.closure {x, y, z}) = gmmn p g 0 1 ζ := by
  have h01 := hx ▸ restrictHom_mem_movedGroup (Subgroup.subset_closure (by simp) :
    x ∈ Subgroup.closure ({x, y, z} : Set (U ≃ₗ[ZMod p] U)))
  have h12 := hz ▸ restrictHom_mem_movedGroup (Subgroup.subset_closure (by simp) :
    z ∈ Subgroup.closure ({x, y, z} : Set (U ≃ₗ[ZMod p] U)))
  have hb1 := hy ▸ restrictHom_mem_movedGroup (Subgroup.subset_closure (by simp) :
    y ∈ Subgroup.closure ({x, y, z} : Set (U ≃ₗ[ZMod p] U)))
  rw [gmmn]
  refine movedGroup_closure_eq ?_ ?_
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · rw [hx]; exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · rw [hy]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
        (Subgroup.subset_closure (Or.inr rfl))
    · rw [hz]; exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  · rintro w (⟨σ, rfl⟩ | hw)
    · exact permMap_mem_of_swap g h01 h12 σ
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      have hdiag : diagMap p g (pairUnit p 0 1 ζ) = permMap p g (Equiv.swap 0 1) *
          (permMap p g (Equiv.swap 0 1) * diagMap p g (pairUnit p 0 1 ζ)) := by
        rw [← mul_assoc, permMap_mul, Equiv.swap_mul_self]
        rw [show permMap p g 1 = 1 from g.ext' fun k => by rw [permMap_apply_basis]; rfl, one_mul]
      rw [hdiag]
      exact Subgroup.mul_mem _ h01 hb1

private theorem exists_gauge_433_three {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U}
    (hφb : φb vb = 2) (hφc : φc vc = 2)
    (h1 : φa vb * φb va = 2) (h2 : φa vc * φc va = 1) (h3 : φb vc * φc vb = 1)
    (h4 : (φa vb - φa vc * φc vb) * (φb va - φc va * φb vc) = 1) :
    ∃ (u : ZMod p) (vb' vc' : U) (φb' φc' : Module.Dual (ZMod p) U) (hb' : φb' vb' = 2)
      (hc' : φc' vc' = 2), u ^ 2 = -1 ∧ Module.reflection hb' = Module.reflection hφb ∧
      Module.reflection hc' = Module.reflection hφc ∧ φa vb' = 1 + u ∧ φb' va = 1 - u ∧
      φa vc' = -1 ∧ φc' va = -1 ∧ φb' vc' = -1 ∧ φc' vb' = -1 := by
  have hs : φa vb * φb vc * φc va + φa vc * φc vb * φb va = 2 := by
    linear_combination h1 + h2 + (φa vc * φc va) * h3 - h4
  have hkk : φa vb * φb vc * φc va * (φa vc * φc vb * φb va) = 2 := by
    linear_combination h1 + (φa vb * φb va) * h2 + (φa vb * φa vc * φb va * φc va) * h3
  have hac0 : φa vc ≠ 0 := left_ne_zero_of_mul (by rw [h2]; exact one_ne_zero)
  have hcb0 : φc vb ≠ 0 := right_ne_zero_of_mul (by rw [h3]; exact one_ne_zero)
  obtain ⟨vb', vc', φb', φc', hb', hc', hrb, hrc, e1, e2, e3, e4, e5, e6, -, -⟩ :=
    exists_starGauge (va := va) (φa := φa) hφb hφc hac0 hcb0
  refine ⟨φa vb * φb vc * φc va - 1, vb', vc', φb', φc', hb', hc', ?_, hrb, hrc, ?_, ?_, e1,
    by rw [e3, h2], by rw [e4, h3], e2⟩
  · linear_combination (φa vb * φb vc * φc va) * hs - hkk
  · rw [h2, h3] at e6
    simpa using e6
  · rw [e5]
    linear_combination hs

private theorem exists_basis_433 [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) = 3)
    {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2)
    (hφc : φc vc = 2) (ha : Module.reflection hφa ∈ H) (hb : Module.reflection hφb ∈ H)
    (hc : Module.reflection hφc ∈ H) {u : ZMod p} (hu : u ^ 2 = -1) (hab : φa vb = 1 + u)
    (hba : φb va = 1 - u) (hac : φa vc = -1) (hca : φc va = -1) (hbc : φb vc = -1)
    (hcb : φc vb = -1) :
    ∃ g : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H),
      ∀ k, (g k : U) = ![(u + 1) • (va - vb), (u - 1) • va - (u + 1) • vb,
        (u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc] k := by
  obtain ⟨⟨pa0, pa1, pa2⟩, ⟨pb0, pb1, pb2⟩, ⟨pc0, pc1, pc2⟩⟩ :=
    pairing_433 hφa hφb hφc hu hab hba hac hca hbc hcb
  have hva := mem_commutatorSpace_of_reflection_mem hp hφa ha
  have hvb := mem_commutatorSpace_of_reflection_mem hp hφb hb
  have hvc := mem_commutatorSpace_of_reflection_mem hp hφc hc
  let e : Fin 3 → U := ![(u + 1) • (va - vb), (u - 1) • va - (u + 1) • vb,
    (u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc]
  have he : ∀ k, e k ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    intro k
    fin_cases k
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hva hvb)
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hva) (Submodule.smul_mem _ _ hvb)
    · exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hva)
        (Submodule.smul_mem _ _ hvb)) (Submodule.smul_mem _ _ hvc)
  let ψ : Fin 3 → Module.Dual (ZMod p) U := ![φa, φb, φc]
  have hdet : (Matrix.of fun i k => ψ i (e k)).det ≠ 0 := by
    have : (Matrix.of fun i k => ψ i (e k)) = !![2, -2, 0; -2 * u, -2, 0; 0, 2, -2] := by
      ext i k
      fin_cases i <;> fin_cases k
      exacts [pa0, pa1, pa2, pb0, pb1, pb2, pc0, pc1, pc2]
    rw [this]
    exact det_433 hp hu
  exact exists_basis_of_pairing hdim he hdet

private theorem restrictHom_433 {H : Subgroup (U ≃ₗ[ZMod p] U)} {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (ha : Module.reflection hφa ∈ H) (hb : Module.reflection hφb ∈ H)
    (hc : Module.reflection hφc ∈ H) {u : ZMod p} (hu : u ^ 2 = -1) (hab : φa vb = 1 + u)
    (hba : φb va = 1 - u) (hac : φa vc = -1) (hca : φc va = -1) (hbc : φb vc = -1)
    (hcb : φc vb = -1)
    (g : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H))
    (hg : ∀ k, (g k : U) = ![(u + 1) • (va - vb), (u - 1) • va - (u + 1) • vb,
      (u - 1) • va - (u + 1) • vb - (2 : ZMod p) • vc] k)
    (ζ : (ZMod p)ˣ) (hζ : (ζ : ZMod p) = -u) :
    restrictHom H _ (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨_, ha⟩ =
        permMap p g (Equiv.swap 0 1) ∧
      restrictHom H _ (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨_, hb⟩ =
        permMap p g (Equiv.swap 0 1) * diagMap p g (pairUnit p 0 1 ζ) ∧
      restrictHom H _ (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨_, hc⟩ =
        permMap p g (Equiv.swap 1 2) := by
  obtain ⟨xa0, xa1, xc1, xc2, xb0, xb1, xa2, xc0, xb2⟩ :=
    action_433 hφa hφb hφc hu hab hba hac hca hbc hcb
  have hζi : ((ζ⁻¹ : (ZMod p)ˣ) : ZMod p) = u := by
    rw [Units.val_inv_eq_inv_val, hζ]
    exact inv_eq_of_mul_eq_one_right (by linear_combination -hu)
  have hpu0 : pairUnit p (0 : Fin 3) 1 ζ 0 = ζ := by simp [pairUnit]
  have hpu1 : pairUnit p (0 : Fin 3) 1 ζ 1 = ζ⁻¹ := by simp [pairUnit]
  have hpu2 : pairUnit p (0 : Fin 3) 1 ζ 2 = 1 := by simp [pairUnit]
  refine ⟨?_, ?_, ?_⟩
  · refine restrictHom_eq_of_basis3 g ha ?_ ?_ ?_ <;> rw [permMap_apply_basis, hg, hg]
    exacts [xa0, xa1, xa2]
  · refine restrictHom_eq_of_basis3 g hb ?_ ?_ ?_ <;>
      rw [LinearEquiv.mul_apply, diagMap_apply_basis, map_smul, permMap_apply_basis,
        Submodule.coe_smul, hg, hg]
    · rw [hpu0, hζ]; exact xb0
    · rw [hpu1, hζi]; exact xb1
    · rw [hpu2, Units.val_one, one_smul]; exact xb2
  · refine restrictHom_eq_of_basis3 g hc ?_ ?_ ?_ <;> rw [permMap_apply_basis, hg, hg]
    exacts [xc0, xc1, xc2]

private theorem pairing_434 {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U}
    (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2) (hab : φa vb = 1) (hba : φb va = 2)
    (hac : φa vc = -1) (hca : φc va = -1) (hbc : φb vc = -2) (hcb : φc vb = -1) :
    (φa (va - vb) = 1 ∧ φa (-vb) = -1 ∧ φa (-vb - vc) = 0) ∧
    (φb (va - vb) = 0 ∧ φb (-vb) = -2 ∧ φb (-vb - vc) = 0) ∧
    (φc (va - vb) = 0 ∧ φc (-vb) = 1 ∧ φc (-vb - vc) = -1) := by
  simp only [map_sub, map_neg, hφa, hφb, hφc, hab, hba, hac, hca, hbc, hcb]
  norm_num

private theorem action_434 {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U}
    (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2) (hab : φa vb = 1) (hba : φb va = 2)
    (hac : φa vc = -1) (hca : φc va = -1) (hbc : φb vc = -2) (hcb : φc vb = -1) :
    Module.reflection hφa (va - vb) = -vb ∧ Module.reflection hφa (-vb) = va - vb ∧
    Module.reflection hφa (-vb - vc) = -vb - vc ∧
    Module.reflection hφb (va - vb) = va - vb ∧ Module.reflection hφb (-vb) = -(-vb) ∧
    Module.reflection hφb (-vb - vc) = -vb - vc ∧
    Module.reflection hφc (va - vb) = va - vb ∧ Module.reflection hφc (-vb) = -vb - vc ∧
    Module.reflection hφc (-vb - vc) = -vb := by
  simp only [Module.reflection_apply, map_sub, map_neg, hφa, hφb, hφc, hab, hba, hac, hca, hbc,
    hcb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> module

theorem movedGroup_eq_g2mmn {x y z : U ≃ₗ[ZMod p] U}
    (g : Module.Basis (Fin 3) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {x, y, z})))
    (hx : restrictHom (Subgroup.closure {x, y, z}) _
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
      ⟨x, Subgroup.subset_closure (by simp)⟩ = permMap p g (Equiv.swap 0 1))
    (hy : restrictHom (Subgroup.closure {x, y, z}) _
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
      ⟨y, Subgroup.subset_closure (by simp)⟩ = diagMap p g (fun i => if i = 1 then -1 else 1))
    (hz : restrictHom (Subgroup.closure {x, y, z}) _
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
      ⟨z, Subgroup.subset_closure (by simp)⟩ = permMap p g (Equiv.swap 1 2)) :
    movedGroup (Subgroup.closure {x, y, z}) = g2mmn p g 0 1 1 := by
  have h01 := hx ▸ restrictHom_mem_movedGroup (Subgroup.subset_closure (by simp) :
    x ∈ Subgroup.closure ({x, y, z} : Set (U ≃ₗ[ZMod p] U)))
  have h12 := hz ▸ restrictHom_mem_movedGroup (Subgroup.subset_closure (by simp) :
    z ∈ Subgroup.closure ({x, y, z} : Set (U ≃ₗ[ZMod p] U)))
  have hb1 := hy ▸ restrictHom_mem_movedGroup (Subgroup.subset_closure (by simp) :
    y ∈ Subgroup.closure ({x, y, z} : Set (U ≃ₗ[ZMod p] U)))
  rw [g2mmn]
  set d0 : Fin 3 → (ZMod p)ˣ := fun i => if i = 0 then -1 else 1
  set d1 : Fin 3 → (ZMod p)ˣ := fun i => if i = 1 then -1 else 1
  have hconj : diagMap p g d1 =
      permMap p g (Equiv.swap 0 1) * diagMap p g d0 * (permMap p g (Equiv.swap 0 1))⁻¹ := by
    rw [permMap_mul_diagMap_mul_inv]
    congr 1
    funext i
    fin_cases i <;> rfl
  refine movedGroup_closure_eq ?_ ?_
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · rw [hx]; exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · rw [hy, hconj]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
        (Subgroup.subset_closure (Or.inr (Set.mem_insert _ _))))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)))
    · rw [hz]; exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  · rintro w (⟨σ, rfl⟩ | hw)
    · exact permMap_mem_of_swap g h01 h12 σ
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · have hD : diagMap p g d0 = (permMap p g (Equiv.swap 0 1))⁻¹ * diagMap p g d1 *
            permMap p g (Equiv.swap 0 1) := by
          rw [hconj]; group
        rw [hD]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h01) hb1) h01
      · rw [pairUnit_one, diagMap_one]
        exact Subgroup.one_mem _

private theorem exists_gauge_434_two (hp : p ≠ 2) {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U} (hφb : φb vb = 2) (hφc : φc vc = 2)
    (h2 : φa vc * φc va = 1) (h3 : φb vc * φc vb = 2)
    (hk : φa vb * φb vc * φc va = 2) (hk' : φa vc * φc vb * φb va = 2) :
    ∃ (vb' vc' : U) (φb' φc' : Module.Dual (ZMod p) U) (hb' : φb' vb' = 2)
      (hc' : φc' vc' = 2), Module.reflection hb' = Module.reflection hφb ∧
      Module.reflection hc' = Module.reflection hφc ∧ φa vb' = 1 ∧ φb' va = 2 ∧
      φa vc' = -1 ∧ φc' va = -1 ∧ φb' vc' = -2 ∧ φc' vb' = -1 := by
  have h2' : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hac0 : φa vc ≠ 0 := left_ne_zero_of_mul (by rw [h2]; exact one_ne_zero)
  have hcb0 : φc vb ≠ 0 := right_ne_zero_of_mul (by rw [h3]; exact h2')
  obtain ⟨vb', vc', φb', φc', hb', hc', hrb, hrc, e1, e2, e3, e4, e5, e6, -, -⟩ :=
    exists_starGauge (va := va) (φa := φa) hφb hφc hac0 hcb0
  refine ⟨vb', vc', φb', φc', hb', hc', hrb, hrc, ?_, by rw [e5, hk'], e1, by rw [e3, h2],
    by rw [e4, h3], e2⟩
  rw [h2, h3, hk] at e6
  have h0 : (2 : ZMod p) * (φa vb' - 1) = 0 := by linear_combination e6
  linear_combination (mul_eq_zero.mp h0).resolve_left h2'

private theorem exists_basis_434 [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) = 3)
    {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2)
    (hφc : φc vc = 2) (ha : Module.reflection hφa ∈ H) (hb : Module.reflection hφb ∈ H)
    (hc : Module.reflection hφc ∈ H) (hab : φa vb = 1) (hba : φb va = 2)
    (hac : φa vc = -1) (hca : φc va = -1) (hbc : φb vc = -2) (hcb : φc vb = -1) :
    ∃ g : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H),
      ∀ k, (g k : U) = ![va - vb, -vb, -vb - vc] k := by
  obtain ⟨⟨pa0, pa1, pa2⟩, ⟨pb0, pb1, pb2⟩, ⟨pc0, pc1, pc2⟩⟩ :=
    pairing_434 hφa hφb hφc hab hba hac hca hbc hcb
  have hva := mem_commutatorSpace_of_reflection_mem hp hφa ha
  have hvb := mem_commutatorSpace_of_reflection_mem hp hφb hb
  have hvc := mem_commutatorSpace_of_reflection_mem hp hφc hc
  let e : Fin 3 → U := ![va - vb, -vb, -vb - vc]
  have he : ∀ k, e k ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    intro k
    fin_cases k
    · exact Submodule.sub_mem _ hva hvb
    · exact Submodule.neg_mem _ hvb
    · exact Submodule.sub_mem _ (Submodule.neg_mem _ hvb) hvc
  let ψ : Fin 3 → Module.Dual (ZMod p) U := ![φa, φb, φc]
  have hdet : (Matrix.of fun i k => ψ i (e k)).det ≠ 0 := by
    have : (Matrix.of fun i k => ψ i (e k)) = !![1, -1, 0; 0, -2, 0; 0, 1, -1] := by
      ext i k
      fin_cases i <;> fin_cases k
      exacts [pa0, pa1, pa2, pb0, pb1, pb2, pc0, pc1, pc2]
    rw [this, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const]
    norm_num
    exact ZMod.prime_ne_zero p 2 hp
  exact exists_basis_of_pairing hdim he hdet

private theorem restrictHom_434 {H : Subgroup (U ≃ₗ[ZMod p] U)} {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (ha : Module.reflection hφa ∈ H) (hb : Module.reflection hφb ∈ H)
    (hc : Module.reflection hφc ∈ H) (hab : φa vb = 1) (hba : φb va = 2)
    (hac : φa vc = -1) (hca : φc va = -1) (hbc : φb vc = -2) (hcb : φc vb = -1)
    (g : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H))
    (hg : ∀ k, (g k : U) = ![va - vb, -vb, -vb - vc] k) :
    restrictHom H _ (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨_, ha⟩ =
        permMap p g (Equiv.swap 0 1) ∧
      restrictHom H _ (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨_, hb⟩ =
        diagMap p g (fun i => if i = 1 then -1 else 1) ∧
      restrictHom H _ (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨_, hc⟩ =
        permMap p g (Equiv.swap 1 2) := by
  obtain ⟨xa0, xa1, xa2, xb0, xb1, xb2, xc0, xc1, xc2⟩ :=
    action_434 hφa hφb hφc hab hba hac hca hbc hcb
  set d1 : Fin 3 → (ZMod p)ˣ := fun i => if i = 1 then -1 else 1
  refine ⟨?_, ?_, ?_⟩
  · refine restrictHom_eq_of_basis3 g ha ?_ ?_ ?_ <;> rw [permMap_apply_basis, hg, hg]
    exacts [xa0, xa1, xa2]
  · refine restrictHom_eq_of_basis3 g hb ?_ ?_ ?_ <;>
      rw [diagMap_apply_basis, hg, Submodule.coe_smul, hg]
    · rw [show d1 0 = 1 from rfl, Units.val_one, one_smul]; exact xb0
    · rw [show d1 1 = -1 from rfl, Units.val_neg, Units.val_one, neg_one_smul]; exact xb1
    · rw [show d1 2 = 1 from rfl, Units.val_one, one_smul]; exact xb2
  · refine restrictHom_eq_of_basis3 g hc ?_ ?_ ?_ <;> rw [permMap_apply_basis, hg, hg]
    exacts [xc0, xc1, xc2]

section RankThree

variable [Module.Finite (ZMod p) U] {a b c : U ≃ₗ[ZMod p] U} {A : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem finrank_movedSpace_sup_le_two {a c : U ≃ₗ[ZMod p] U} (ha : IsRefl p a)
    (hc : IsRefl p c) :
    Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.movedSpace a ⊔ HardMathSupport.Kantor79.movedSpace c) ≤ 2 := by
  have h1 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace a) = 1 := by
    change Module.finrank (ZMod p)
      (LinearMap.range ((a : U →ₗ[ZMod p] U) - LinearMap.id)) = 1
    exact ha.2
  have h2 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace c) = 1 := by
    change Module.finrank (ZMod p)
      (LinearMap.range ((c : U →ₗ[ZMod p] U) - LinearMap.id)) = 1
    exact hc.2
  calc Module.finrank (ZMod p)
        ↥(HardMathSupport.Kantor79.movedSpace a ⊔ HardMathSupport.Kantor79.movedSpace c)
      ≤ Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace a) +
          Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace c) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ = 2 := by rw [h1, h2]

omit [Module.Finite (ZMod p) U] in
private theorem commutatorSpace_closure_pair_le {a c : U ≃ₗ[ZMod p] U} :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure ({a, c} : Set (U ≃ₗ[ZMod p] U)))
      ≤ HardMathSupport.Kantor79.movedSpace a ⊔ HardMathSupport.Kantor79.movedSpace c := by
  rw [commutatorSpace_le_iff]
  refine fun g hg v => ?_
  have key : ∀ g ∈ Subgroup.closure ({a, c} : Set (U ≃ₗ[ZMod p] U)),
      ∀ v, g v - v ∈ HardMathSupport.Kantor79.movedSpace a ⊔
        HardMathSupport.Kantor79.movedSpace c := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem t ht =>
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · intro v; exact Submodule.mem_sup_left ⟨v, rfl⟩
      · intro v; exact Submodule.mem_sup_right ⟨v, rfl⟩
    | one => intro v; simp
    | mul x y _ _ ihx ihy =>
      intro v
      have h1 := ihx (y v)
      have h2 := ihy v
      rw [LinearEquiv.mul_apply]
      rw [show x (y v) - v = (x (y v) - y v) + (y v - v) by abel]
      exact add_mem h1 h2
    | inv x _ ihx =>
      intro v
      have h1 := ihx (x⁻¹ v)
      have h2 : x⁻¹ v - v = -(x (x⁻¹ v) - x⁻¹ v) := by
        have hx : x (x⁻¹ v) = v := by simp
        rw [hx]; abel
      rw [h2]; exact neg_mem h1
  exact key g hg v

private theorem two_le_orderOf_cacb_aux {a b c : U ≃ₗ[ZMod p] U}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c)
    (hA : A = Subgroup.closure {a, b, c})
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace A) = 3) :
    2 ≤ orderOf (c * a * c * b) := by
  by_contra hcon
  push Not at hcon
  have hfinU : Finite U := Module.finite_of_finite (ZMod p)
  have hfinU' : Fintype U := Fintype.ofFinite U
  have hfinG : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  have h1 : orderOf (c * a * c * b) = 1 := by
    have := orderOf_pos (c * a * c * b); omega
  have hone : c * a * c * b = 1 := orderOf_eq_one_iff.mp h1
  have hcac_eq : c * a * c = b := by
    calc c * a * c = (c * a * c) * (b * b) := by rw [hb.1, mul_one]
      _ = ((c * a * c) * b) * b := by group
      _ = b := by rw [hone, one_mul]
  have hb_mem : b ∈ Subgroup.closure ({a, c} : Set (U ≃ₗ[ZMod p] U)) := by
    rw [← hcac_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  have hA' : A = Subgroup.closure ({a, c} : Set (U ≃ₗ[ZMod p] U)) := by
    rw [hA]
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact hb_mem
      · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.closure_mono (by
        intro x hx
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> simp)
  have hle := commutatorSpace_closure_pair_le (a := a) (c := c)
  have hfin : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure ({a, c} : Set (U ≃ₗ[ZMod p] U)))) ≤ 2 :=
    (Submodule.finrank_mono hle).trans (finrank_movedSpace_sup_le_two ha hc)
  rw [hA'] at hdim
  omega

theorem two_le_orderOf_cacb (hp : p ≠ 2) (_hU : Module.finrank (ZMod p) U = 4)
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c) (hA : A = Subgroup.closure {a, b, c})
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace A) = 3)
    (hd : DMax p A 4) : 2 ≤ orderOf (c * a * c * b) ∧ orderOf (c * a * c * b) ≤ 4 := by
  have hmemb : b ∈ A := by rw [hA]; exact Subgroup.subset_closure (by simp)
  have hmemc : c ∈ A := by rw [hA]; exact Subgroup.subset_closure (by simp)
  have hcacA : c * a * c ∈ A := A.mul_mem (A.mul_mem hmemc (by
    rw [hA]; exact Subgroup.subset_closure (by simp))) hmemc
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc.1
  have href : IsRefl p (c * a * c) := by
    simpa [hcinv] using isRefl_conj_of_isRefl (g := c) hp ha
  exact ⟨two_le_orderOf_cacb_aux ha hb hc hA hdim, hd.1 (c * a * c) hcacA b hmemb href hb⟩

theorem orderOf_cacb_ne_two_of_433 (hp : p ≠ 2) (_hU : Module.finrank (ZMod p) U = 4)
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c) (_hA : A = Subgroup.closure {a, b, c})
    (_hAt : QTwoLin.TransvectionFree A)
    (_hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace A) = 3)
    (_hd : DMax p A 4) (hab : orderOf (a * b) = 4) (hac : orderOf (a * c) = 3)
    (hbc : orderOf (b * c) = 3) : orderOf (c * a * c * b) ≠ 2 := by
  obtain ⟨va, φa, hφa, rfl⟩ := (isRefl_iff hp a).mp ha
  obtain ⟨vb, φb, hφb, rfl⟩ := (isRefl_iff hp b).mp hb
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp hc
  intro hm
  have h1 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb hab
  have h2 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφa hφc hac
  have h3 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφb hφc hbc
  rw [reflection_conj_reflection hφc hφa] at hm
  obtain ⟨E1, E2⟩ := apply_eq_zero_of_orderOf_eq_two hp _ hφb hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at E1 E2
  exact one_ne_zero (by
    linear_combination (φb va) * E1 + (φa vc * φc vb) * E2 - h1 + (φb vc * φc vb) * h2 + h3 :
      (1 : ZMod p) = 0)

theorem eq_gmmn_of_433 (hp : p ≠ 2) (_hU : Module.finrank (ZMod p) U = 4)
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c) (hA : A = Subgroup.closure {a, b, c})
    (_hAt : QTwoLin.TransvectionFree A)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace A) = 3)
    (_hd : DMax p A 4) (hab : orderOf (a * b) = 4) (hac : orderOf (a * c) = 3)
    (hbc : orderOf (b * c) = 3) (hm : orderOf (c * a * c * b) = 3) :
    SplitSupport A 3 ∧ ∃ (g : Module.Basis (Fin 3) (ZMod p)
        (HardMathSupport.Kantor79.commutatorSpace A)) (ζ : (ZMod p)ˣ),
      orderOf ζ = 4 ∧ movedGroup A = gmmn p g 0 1 ζ := by
  obtain ⟨va, φa, hφa, rfl⟩ := (isRefl_iff hp a).mp ha
  obtain ⟨vb, φb, hφb, rfl⟩ := (isRefl_iff hp b).mp hb
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp hc
  have h1 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb hab
  have h2 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφa hφc hac
  have h3 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφb hφc hbc
  rw [reflection_conj_reflection hφc hφa] at hm
  have h4 := apply_mul_apply_eq_one_of_orderOf_eq_three hp _ hφb hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at h4
  have h2' : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  refine ⟨?_, ?_⟩
  · rw [hA]
    refine splitSupport_closure_three hφa hφb hφc (by rw [h1]; exact h2')
      (by rw [h2]; exact one_ne_zero) (by rw [h3]; exact one_ne_zero) ?_
    rw [h1, h2, h3, show φa vb * φb vc * φc va + φa vc * φc vb * φb va = 2 by
      linear_combination h1 + h2 + (φa vc * φc va) * h3 - h4]
    norm_num
    exact h2'
  obtain ⟨u, vb', vc', φb', φc', hb', hc', hu, hrb, hrc, hab', hba', e1, hca', hbc', e2⟩ :=
    exists_gauge_433_three hφb hφc h1 h2 h3 h4
  rw [← hrb, ← hrc] at hA
  subst hA
  set S : Set (U ≃ₗ[ZMod p] U) := {Module.reflection hφa, Module.reflection hb',
    Module.reflection hc'} with hS
  have hma : Module.reflection hφa ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
  have hmb : Module.reflection hb' ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
  have hmc : Module.reflection hc' ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
  obtain ⟨g, hg⟩ := exists_basis_433 hp hdim hφa hb' hc' hma hmb hmc hu hab' hba' e1 hca' hbc' e2
  have hu0 : -u ≠ 0 := by
    intro h0
    have : u = 0 := by linear_combination -h0
    rw [this] at hu
    exact one_ne_zero (by linear_combination hu : (1 : ZMod p) = 0)
  refine ⟨g, Units.mk0 (-u) hu0, orderOf_unit_eq_four hp (by
    rw [Units.val_mk0]; linear_combination hu), ?_⟩
  obtain ⟨hra, hrb', hrc'⟩ := restrictHom_433 hφa hb' hc' hma hmb hmc hu hab' hba' e1 hca' hbc'
    e2 g hg (Units.mk0 (-u) hu0) rfl
  exact movedGroup_eq_gmmn g _ hra hrb' hrc'

theorem eq_g2mmn_of_434 (hp : p ≠ 2) (_hU : Module.finrank (ZMod p) U = 4)
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c) (hA : A = Subgroup.closure {a, b, c})
    (_hAt : QTwoLin.TransvectionFree A)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace A) = 3)
    (_hd : DMax p A 4) (hab : orderOf (a * b) = 4) (hac : orderOf (a * c) = 3)
    (hbc : orderOf (b * c) = 4) (hm : orderOf (c * a * c * b) = 2) :
    SplitSupport A 3 ∧ ∃ g : Module.Basis (Fin 3) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace A), movedGroup A = g2mmn p g 0 1 1 := by
  obtain ⟨va, φa, hφa, rfl⟩ := (isRefl_iff hp a).mp ha
  obtain ⟨vb, φb, hφb, rfl⟩ := (isRefl_iff hp b).mp hb
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp hc
  have h1 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb hab
  have h2 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφa hφc hac
  have h3 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφb hφc hbc
  rw [reflection_conj_reflection hφc hφa] at hm
  obtain ⟨E1, E2⟩ := apply_eq_zero_of_orderOf_eq_two hp _ hφb hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at E1 E2
  have hk : φa vb * φb vc * φc va = 2 := by
    linear_combination (φb vc * φc va) * E1 + (φb vc * φc vb) * h2 + h3
  have hk' : φa vc * φc vb * φb va = 2 := by
    linear_combination (φa vc * φc vb) * E2 + (φb vc * φc vb) * h2 + h3
  have h2' : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  refine ⟨?_, ?_⟩
  · rw [hA]
    refine splitSupport_closure_three hφa hφb hφc (by rw [h1]; exact h2')
      (by rw [h2]; exact one_ne_zero) (by rw [h3]; exact h2') ?_
    rw [h1, h2, h3, hk, hk']; norm_num; exact h2'
  obtain ⟨vb', vc', φb', φc', hb', hc', hrb, hrc, hab', hba', e1, hca', hbc', e2⟩ :=
    exists_gauge_434_two hp hφb hφc h2 h3 hk hk'
  rw [← hrb, ← hrc] at hA
  subst hA
  set S : Set (U ≃ₗ[ZMod p] U) := {Module.reflection hφa, Module.reflection hb',
    Module.reflection hc'} with hS
  have hma : Module.reflection hφa ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
  have hmb : Module.reflection hb' ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
  have hmc : Module.reflection hc' ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
  obtain ⟨g, hg⟩ := exists_basis_434 hp hdim hφa hb' hc' hma hmb hmc hab' hba' e1 hca' hbc' e2
  obtain ⟨hra, hrb', hrc'⟩ := restrictHom_434 hφa hb' hc' hma hmb hmc hab' hba' e1 hca' hbc' e2 g hg
  exact ⟨g, movedGroup_eq_g2mmn g hra hrb' hrc'⟩

theorem commute_of_434 (hp : p ≠ 2) (_hU : Module.finrank (ZMod p) U = 4)
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c) (hA : A = Subgroup.closure {a, b, c})
    (_hAt : QTwoLin.TransvectionFree A)
    (_hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace A) = 3)
    (hd : DMax p A 4) (hab : orderOf (a * b) = 4) (hac : orderOf (a * c) = 3)
    (hbc : orderOf (b * c) = 4) (hm : orderOf (c * a * c * b) = 4) :
    p = 3 ∧ b * c * b * a = a * (b * c * b) := by
  have hmema : a ∈ A := by rw [hA]; exact Subgroup.subset_closure (by simp)
  have hmemb : b ∈ A := by rw [hA]; exact Subgroup.subset_closure (by simp)
  have hmemc : c ∈ A := by rw [hA]; exact Subgroup.subset_closure (by simp)
  have hbcb : b * c * b ∈ A := A.mul_mem (A.mul_mem hmemb hmemc) hmemb
  obtain ⟨va, φa, hφa, rfl⟩ := (isRefl_iff hp a).mp ha
  obtain ⟨vb, φb, hφb, rfl⟩ := (isRefl_iff hp b).mp hb
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp hc
  have hx := hd.1 _ hbcb _ hmema
    (by rw [reflection_conj_reflection hφb hφc]; exact isRefl_reflection hp _) ha
  have h1 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb hab
  have h2 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφa hφc hac
  have h3 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφb hφc hbc
  rw [reflection_conj_reflection hφc hφa] at hm
  have h4 := apply_mul_apply_eq_two_of_orderOf_eq_four hp _ hφb hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at h4
  have hη : (φc - φc vb • φb) va * φa (vc - φb vc • vb) = 3 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
    linear_combination h1 - h2 + (φa vb * φb va - φa vc * φc va) * h3 + h4
  rw [reflection_conj_reflection hφb hφc] at hx ⊢
  have h2' : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rcases eta_cases_of_orderOf_le_four hp _ hφa hx with ⟨z1, z2⟩ | h | h | ⟨-, h⟩
  · refine ⟨?_, reflection_mul_comm_of_apply_eq_zero _ hφa z1 z2⟩
    rw [z1, zero_mul] at hη
    have h3n : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -hη
    rw [ZMod.natCast_eq_zero_iff] at h3n
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h3n
  · exact absurd (by linear_combination h - hη : (2 : ZMod p) = 0) h2'
  · exact absurd (by linear_combination h - hη : (1 : ZMod p) = 0) one_ne_zero
  · exact absurd (by linear_combination hη - h : (1 : ZMod p) = 0) one_ne_zero

end RankThree

end CFSG.StandardType.ZS

end
