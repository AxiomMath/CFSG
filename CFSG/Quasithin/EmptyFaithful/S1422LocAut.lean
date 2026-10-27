module

import all CFSG.Quasithin.Recognition.U33Defs
public import CFSG.Quasithin.Recognition.U33Defs

public section

namespace CFSG.Quasithin

theorem z4q8_card_central :
    Fintype.card {c : Z4StarQ8Model // ∀ q : Z4StarQ8Model, c * q = q * c} = 4 := by decide

theorem z4q8_comm_mem (x y : Z4StarQ8Model) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = ⟨2, 0, 0⟩ := by
  revert x y
  decide

theorem z4q8_central_involution (c : Z4StarQ8Model) (hc : ∀ q : Z4StarQ8Model, c * q = q * c)
    (hc2 : c * c = 1) : c = 1 ∨ c = ⟨2, 0, 0⟩ := by
  revert c
  decide

@[expose] def z4q8GenRel (t : Z4StarQ8Model × Z4StarQ8Model × Z4StarQ8Model) : Prop :=
  t.1 * t.1 * t.1 * t.1 = 1 ∧ t.1 * t.1 ≠ 1 ∧ t.1 * t.2.1 = t.2.1 * t.1 ∧
    t.1 * t.2.2 = t.2.2 * t.1 ∧ t.2.1 * t.2.1 = 1 ∧ t.2.2 * t.2.2 = 1 ∧
    t.2.2 * t.2.1 * t.2.2⁻¹ * t.2.1⁻¹ = t.1 * t.1

instance : DecidablePred z4q8GenRel := fun t => by unfold z4q8GenRel; infer_instance

theorem z4q8_card_genRel : Fintype.card {t : Z4StarQ8Model × Z4StarQ8Model × Z4StarQ8Model //
    z4q8GenRel t} = 48 := by decide +kernel

@[expose] def z4q8g1 : Z4StarQ8Model := ⟨1, 0, 0⟩

@[expose] def z4q8g2 : Z4StarQ8Model := ⟨0, 1, 0⟩

@[expose] def z4q8g3 : Z4StarQ8Model := ⟨0, 0, 1⟩

theorem z4q8_gen (x : Z4StarQ8Model) :
    ∃ a < 4, ∃ b < 2, ∃ c < 2, x = z4q8g1 ^ a * z4q8g2 ^ b * z4q8g3 ^ c := by
  revert x
  decide

theorem card_mulAut_z4StarQ8Model_le : Nat.card (MulAut Z4StarQ8Model) ≤ 48 := by
  classical
  have hrel : ∀ σ : MulAut Z4StarQ8Model, z4q8GenRel (σ z4q8g1, σ z4q8g2, σ z4q8g3) := by
    intro σ
    have e1 : z4q8g1 * z4q8g1 * z4q8g1 * z4q8g1 = 1 := by decide
    have e2 : z4q8g1 * z4q8g1 ≠ 1 := by decide
    have e3 : z4q8g1 * z4q8g2 = z4q8g2 * z4q8g1 := by decide
    have e4 : z4q8g1 * z4q8g3 = z4q8g3 * z4q8g1 := by decide
    have e5 : z4q8g2 * z4q8g2 = 1 := by decide
    have e6 : z4q8g3 * z4q8g3 = 1 := by decide
    have e7 : z4q8g3 * z4q8g2 * z4q8g3⁻¹ * z4q8g2⁻¹ = z4q8g1 * z4q8g1 := by decide
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := congrArg σ e1
      simpa only [map_mul, map_one] using this
    · intro h
      apply e2
      apply σ.injective
      have : σ (z4q8g1 * z4q8g1) = 1 := by simpa only [map_mul] using h
      rw [this, map_one]
    · have := congrArg σ e3
      simpa only [map_mul] using this
    · have := congrArg σ e4
      simpa only [map_mul] using this
    · have := congrArg σ e5
      simpa only [map_mul, map_one] using this
    · have := congrArg σ e6
      simpa only [map_mul, map_one] using this
    · have := congrArg σ e7
      simpa only [map_mul, map_inv] using this
  have hinj : Function.Injective fun σ : MulAut Z4StarQ8Model =>
      (⟨(σ z4q8g1, σ z4q8g2, σ z4q8g3), hrel σ⟩ :
        {t : Z4StarQ8Model × Z4StarQ8Model × Z4StarQ8Model // z4q8GenRel t}) := by
    intro σ τ h
    have h1 : σ z4q8g1 = τ z4q8g1 := congrArg (fun t => t.1.1) h
    have h2 : σ z4q8g2 = τ z4q8g2 := congrArg (fun t => t.1.2.1) h
    have h3 : σ z4q8g3 = τ z4q8g3 := congrArg (fun t => t.1.2.2) h
    refine MulEquiv.ext fun x => ?_
    obtain ⟨a, -, b, -, c, -, hx⟩ := z4q8_gen x
    rw [hx, map_mul, map_mul, map_pow, map_pow, map_pow, map_mul, map_mul, map_pow, map_pow,
      map_pow, h1, h2, h3]
  calc Nat.card (MulAut Z4StarQ8Model)
      ≤ Nat.card {t : Z4StarQ8Model × Z4StarQ8Model × Z4StarQ8Model // z4q8GenRel t} :=
        Nat.card_le_card_of_injective _ hinj
    _ = 48 := by rw [Nat.card_eq_fintype_card, z4q8_card_genRel]

end CFSG.Quasithin
