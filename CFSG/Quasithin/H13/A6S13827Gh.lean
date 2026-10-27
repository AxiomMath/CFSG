module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.H13.A6.A6G2

theorem pow_four_conj_eq {Γ : Type*} [Group Γ] {h n d e : Γ} (hn : h * n * h⁻¹ = d * n)
    (hd : h * d * h⁻¹ = e * d) (he : h * e * h⁻¹ = e) (hd2 : d * d = 1) (he2 : e * e = 1) :
    h ^ 4 * n * (h ^ 4)⁻¹ = n := by
  have h2n : h ^ 2 * n * (h ^ 2)⁻¹ = e * n := by
    calc h ^ 2 * n * (h ^ 2)⁻¹ = h * (h * n * h⁻¹) * h⁻¹ := by rw [pow_two]; group
      _ = h * (d * n) * h⁻¹ := by rw [hn]
      _ = (h * d * h⁻¹) * (h * n * h⁻¹) := by group
      _ = e * d * (d * n) := by rw [hd, hn]
      _ = e * n := by rw [mul_assoc e d, ← mul_assoc d d, hd2, one_mul]
  have h2e : h ^ 2 * e * (h ^ 2)⁻¹ = e := by
    calc h ^ 2 * e * (h ^ 2)⁻¹ = h * (h * e * h⁻¹) * h⁻¹ := by rw [pow_two]; group
      _ = e := by rw [he, he]
  calc h ^ 4 * n * (h ^ 4)⁻¹ = h ^ 2 * (h ^ 2 * n * (h ^ 2)⁻¹) * (h ^ 2)⁻¹ := by
        rw [show h ^ 4 = h ^ 2 * h ^ 2 by rw [← pow_add]]; group
    _ = h ^ 2 * (e * n) * (h ^ 2)⁻¹ := by rw [h2n]
    _ = (h ^ 2 * e * (h ^ 2)⁻¹) * (h ^ 2 * n * (h ^ 2)⁻¹) := by group
    _ = e * (e * n) := by rw [h2e, h2n]
    _ = n := by rw [← mul_assoc, he2, one_mul]

theorem card_le_four_of_lt {Γ : Type*} [Group Γ] {A B : Subgroup Γ} [Finite ↥B] (hAB : A ≤ B)
    (hne : A ≠ B) (hB : Nat.card B ≤ 8) : Nat.card A ≤ 4 := by
  have : Finite ↥A := Finite.of_injective _ (Subgroup.inclusion_injective hAB)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hAB
  have hlt : Nat.card A < Nat.card B := Subgroup.card_lt_of_lt (lt_of_le_of_ne hAB hne)
  have hA0 : 0 < Nat.card A := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k
    · rw [mul_zero] at hk
      omega
    · rw [mul_one] at hk
      omega
  nlinarith

theorem comm_mem_of_relIndex_dvd_two {Γ : Type*} [Group Γ] {V₁ W : Subgroup Γ}
    (hi : V₁.relIndex W ∣ 2) {h : Γ} (hW : h ∈ Subgroup.normalizer (W : Set Γ))
    (hV : h ∈ Subgroup.normalizer (V₁ : Set Γ)) {w : Γ} (hw : w ∈ W) :
    h * w * h⁻¹ * w⁻¹ ∈ V₁ := by
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_dvd_two_iff.1 hi
  have hw' : h * w * h⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hW w).mp hw
  by_cases hwV : w ∈ V₁
  · exact V₁.mul_mem ((Subgroup.mem_normalizer_iff.mp hV w).mp hwV) (V₁.inv_mem hwV)
  · have hw'V : h * w * h⁻¹ ∉ V₁ := fun h1 => hwV ((Subgroup.mem_normalizer_iff.mp hV w).mpr h1)
    have h1 := (ha w hw).resolve_right hwV
    have h2 := (ha _ hw').resolve_right hw'V
    have e : h * w * h⁻¹ * w⁻¹ = (h * w * h⁻¹ * a) * (w * a)⁻¹ := by group
    rw [e]
    exact V₁.mul_mem h2 (V₁.inv_mem h1)

theorem exists_hom_two_of_not_mem {E : Type} [CommGroup E] [Finite E] (hE : ∀ w : E, w ^ 2 = 1)
    {D : Subgroup E} {c : E} (hc : c ∉ D) :
    ∃ f : E →* Multiplicative (ZMod 2), (∀ d ∈ D, f d = 1) ∧ f c ≠ 1 := by
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule (n := 2) fun x => by
    have := hE (Additive.toMul x)
    apply Additive.toMul.injective
    rw [toMul_nsmul, this, toMul_zero]
  let D' : Submodule (ZMod 2) (Additive E) :=
    { carrier := {x | Additive.toMul x ∈ D}
      add_mem' := fun ha hb => D.mul_mem ha hb
      zero_mem' := D.one_mem
      smul_mem' := fun r x hx => by
        fin_cases r
        · show Additive.toMul ((0 : ZMod 2) • x) ∈ D
          rw [zero_smul]
          exact D.one_mem
        · show Additive.toMul ((1 : ZMod 2) • x) ∈ D
          rw [one_smul]
          exact hx }
  have hc' : Submodule.Quotient.mk (p := D') (Additive.ofMul c) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hc
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (Additive E ⧸ D'),
      φ (Submodule.Quotient.mk (Additive.ofMul c)) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc' ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 hall)
  let f : E →* Multiplicative (ZMod 2) :=
    { toFun := fun w => Multiplicative.ofAdd (φ (D'.mkQ (Additive.ofMul w)))
      map_one' := by
        show Multiplicative.ofAdd (φ (D'.mkQ 0)) = 1
        rw [map_zero, map_zero]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (φ (D'.mkQ (Additive.ofMul a + Additive.ofMul b))) = _
        rw [map_add, map_add, ofAdd_add] }
  refine ⟨f, fun d hd => ?_, fun h1 => hφ ?_⟩
  · have h0 : D'.mkQ (Additive.ofMul d) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hd
    show Multiplicative.ofAdd (φ (D'.mkQ (Additive.ofMul d))) = 1
    rw [h0, map_zero]
    rfl
  · have : Multiplicative.ofAdd (φ (D'.mkQ (Additive.ofMul c))) = 1 := h1
    exact this

end CFSG.Quasithin.H13.A6.A6G2
