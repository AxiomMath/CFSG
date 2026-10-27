module

public import CFSG.Milestones.ASVolI.H13

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open scoped Pointwise

@[expose] def fixOct (l : Finset (Finset (Fin 24))) : Subgroup S24 :=
  M24g ⊓ ⨅ O ∈ l, MulAction.stabilizer S24 O

theorem mem_fixOct {l : Finset (Finset (Fin 24))} {σ : S24} :
    σ ∈ fixOct l ↔ σ ∈ M24g ∧ ∀ O ∈ l, σ • O = O := by
  simp only [fixOct, Subgroup.mem_inf, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

theorem fixOct_le_M24g (l : Finset (Finset (Fin 24))) : fixOct l ≤ M24g := inf_le_left

theorem fixOct_conj_iff {l : Finset (Finset (Fin 24))} {σ τ : S24} (hσ : σ ∈ M24g) :
    τ ∈ fixOct l ↔ σ * τ * σ⁻¹ ∈ fixOct (σ • l) := by
  rw [mem_fixOct, mem_fixOct]
  constructor
  · rintro ⟨hτ, hfix⟩
    refine ⟨Subgroup.mul_mem M24g (Subgroup.mul_mem M24g hσ hτ) (Subgroup.inv_mem M24g hσ), ?_⟩
    intro O hO
    obtain ⟨O', hO', rfl⟩ := Finset.mem_smul_finset.1 hO
    rw [mul_smul, mul_smul, inv_smul_smul, hfix O' hO']
  · rintro ⟨hconj, hfix⟩
    have hτ : τ ∈ M24g := by
      have h0 : σ⁻¹ * (σ * τ * σ⁻¹) * σ ∈ M24g :=
        Subgroup.mul_mem M24g
          (Subgroup.mul_mem M24g (Subgroup.inv_mem M24g hσ) hconj) hσ
      rwa [show σ⁻¹ * (σ * τ * σ⁻¹) * σ = τ by simp [mul_assoc]] at h0
    refine ⟨hτ, ?_⟩
    intro O' hO'
    have hmem : σ • O' ∈ σ • l := Finset.smul_mem_smul_finset (a := σ) hO'
    have h := hfix (σ • O') hmem
    refine smul_left_cancel σ ?_
    simpa [mul_smul] using h

@[expose] def FixOctPerfect : Prop :=
  ∀ l : Finset (Finset (Fin 24)), IsTrio l → ⁅fixOct l, fixOct l⁆ = fixOct l

@[expose] def FixOctSym : Prop :=
  ∀ l : Finset (Finset (Fin 24)), IsTrio l → ∀ π : Equiv.Perm ↥l,
    ∃ σ ∈ M24g, ∀ O : ↥l, σ • (O : Finset (Fin 24)) = ((π O : ↥l) : Finset (Fin 24))

@[expose] def FixOctCommW11 : Prop :=
  ∀ l : Finset (Finset (Fin 24)), IsTrio l →
    2 ^ 9 ≤ Nat.card ↥(Subgroup.closure {x : W11 | ∃ (w : W11) (σ : ↥AutPerm),
      (σ : S24) ∈ fixOct l ∧ x = w * (rho11 AutPerm le_rfl σ w)⁻¹})

end CFSG.Quasithin.H13.AS91
