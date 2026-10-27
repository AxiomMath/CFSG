module

public import CFSG.Quasithin.Recognition.RuTypeSigma

public section

namespace CFSG.Quasithin.RuType

open scoped MatrixGroups

namespace Sigma47

@[expose] def NormBy (x σ : SigmaL2F4) : Prop := ∃ k : Fin 5, x * σ * x⁻¹ = σ ^ (k : ℕ)

instance (x σ : SigmaL2F4) : Decidable (NormBy x σ) := by
  unfold NormBy
  infer_instance

@[expose] def PowOf (σ τ : SigmaL2F4) : Prop := ∃ k : Fin 5, τ = σ ^ (k : ℕ)

instance (σ τ : SigmaL2F4) : Decidable (PowOf σ τ) := by
  unfold PowOf
  infer_instance

@[expose] def d0 : SigmaL2F4 := ⟨⟨!![1, 1; 0, 1], by decide⟩, 1⟩

@[expose] def σa : SigmaL2F4 := ⟨⟨!![0, ⟨2⟩; ⟨3⟩, ⟨3⟩], by decide⟩, 1⟩

@[expose] def σb : SigmaL2F4 := ⟨⟨!![0, ⟨3⟩; ⟨2⟩, ⟨2⟩], by decide⟩, 1⟩

theorem σa_pow_five : σa ^ 5 = 1 ∧ σa ≠ 1 := by decide +kernel

theorem σb_pow_five : σb ^ 5 = 1 ∧ σb ≠ 1 := by decide +kernel

theorem not_powOf_σa_σb : ¬ PowOf σa σb := by decide +kernel

theorem normBy_d0_iff : ∀ τ : SigmaL2F4, τ ^ 5 = 1 → τ ≠ 1 → NormBy d0 τ →
    PowOf σa τ ∨ PowOf σb τ := by
  decide +kernel

theorem eq_one_of_comm_d0_of_pow_three : ∀ c : SigmaL2F4, c * d0 = d0 * c → c ^ 3 = 1 →
    c = 1 := by
  decide +kernel

theorem swap_of_comm_d0 : ∀ c : SigmaL2F4, c * d0 = d0 * c → c * c = 1 → c ≠ 1 → c ≠ d0 →
    PowOf σb (c * σa * c⁻¹) := by
  decide +kernel

theorem right_eq_one_of_normBy : ∀ d σ : SigmaL2F4, d * d = 1 → d ≠ 1 → σ ^ 5 = 1 → σ ≠ 1 →
    NormBy d σ → d.right = 1 := by
  decide +kernel

theorem exists_conj_d0_of_right : ∀ d : SigmaL2F4, d * d = 1 → d ≠ 1 → d.right = 1 →
    ∃ g : SigmaL2F4, d = g * d0 * g⁻¹ := by
  decide +kernel

theorem exists_conj_d0 {d σ : SigmaL2F4} (hd : d * d = 1) (hd1 : d ≠ 1) (hσ : σ ^ 5 = 1)
    (hσ1 : σ ≠ 1) (hN : NormBy d σ) : ∃ g : SigmaL2F4, d = g * d0 * g⁻¹ :=
  exists_conj_d0_of_right d hd hd1 (right_eq_one_of_normBy d σ hd hd1 hσ hσ1 hN)

end Sigma47

end CFSG.Quasithin.RuType
