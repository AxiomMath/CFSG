module

public import CFSG.LieType.SeitzGeneration.UnitaryCenters
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterAntiFrame

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.SeitzGeneration.Centers

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem isCenter_of_antiFrame (hσ : IsUnitaryInvolution σ) {H : Subgroup (SUid σ 4)}
    {A A' : Matrix (Fin 4) (Fin 4) K} {l : K} (hl : σ l * l = -1)
    (hAu : (A.map σ)ᵀ * A = 1) (hA'u : (A'.map σ)ᵀ * A' = 1) {f₁ f₂ g₁ g₂ : Fin 4 → K}
    (F : AntiFrame σ A A' l f₁ f₂ g₁ g₂)
    (hH : ∀ g : SUid σ 4,
      (A * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (g : GL (Fin 4) K) * A ∨
        A' * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (g : GL (Fin 4) K) * A') →
      g ∈ H) :
    IsCenter H f₁ := by
  refine ⟨F.f₁f₁, ?_⟩
  intro c hc
  obtain ⟨d, hd⟩ := hσ.exists_sub_eq hc
  have hc₁ : (0 : K) + σ 0 = -herm σ g₂ g₂ := by simp [F.g₂g₂]
  have hc₂ : (0 : K) + σ 0 = -herm σ (d • f₂) (d • f₂) := by simp [F.f₂f₂]
  have hf₁df₂ : herm σ f₁ (d • f₂) = 0 := by
    rw [herm_smul_right, F.f₁f₂, mul_zero]
  let E₁ : SUid σ 4 := eichler hσ.invol F.f₁f₁ F.f₁g₂ hc₁
  let E₂ : SUid σ 4 := eichler hσ.invol F.f₁f₁ hf₁df₂ hc₂
  have hE₁A : A * ((E₁ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((E₁ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A :=
    eichlerMat_comm_of_eigen hσ.invol hl (Or.inl rfl) hAu F.f₁f₁ F.af₁ F.ag₂
  have hE₂y : A' *ᵥ (d • f₂) = (-l) • (d • f₂) := by
    rw [Matrix.mulVec_smul, F.bf₂, smul_smul, smul_smul, mul_comm]
  have hE₂A : A' * ((E₂ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((E₂ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A' :=
    eichlerMat_comm_of_eigen hσ.invol hl (Or.inl rfl) hA'u F.f₁f₁ F.bf₁ hE₂y
  have hE₁H : E₁ ∈ H := hH E₁ (Or.inl hE₁A)
  have hE₂H : E₂ ∈ H := hH E₂ (Or.inr hE₂A)
  have hg₂f₂ : herm σ g₂ f₂ = 1 := by
    rw [herm_conj σ hσ.invol, F.f₂g₂, map_one]
  have hcoef : herm σ (d • f₂) g₂ - herm σ g₂ (d • f₂) = c := by
    rw [herm_smul_left, herm_smul_right, F.f₂g₂, hg₂f₂]
    simpa using hd
  have ht : (herm σ (d • f₂) g₂ - herm σ g₂ (d • f₂)) +
      σ (herm σ (d • f₂) g₂ - herm σ g₂ (d • f₂)) = 0 := by
    rw [hcoef]
    exact hc
  have hkey := eichler_mul_eichler hσ.invol F.f₁f₁ F.f₁g₂ hf₁df₂ hc₁ hc₂ ht
  have htv : tv hσ.invol F.f₁f₁ ht = tv hσ.invol F.f₁f₁ hc := by
    apply ext_smul
    intro v
    rw [tv_smul, tv_smul, hcoef]
  refine ⟨E₁ * E₂ * E₁⁻¹ * E₂⁻¹,
    H.mul_mem (H.mul_mem (H.mul_mem hE₁H hE₂H) (H.inv_mem hE₁H)) (H.inv_mem hE₂H), ?_⟩
  intro v
  have hg : E₁ * E₂ * E₁⁻¹ * E₂⁻¹ = tv hσ.invol F.f₁f₁ ht := by
    change eichler hσ.invol F.f₁f₁ F.f₁g₂ hc₁ * eichler hσ.invol F.f₁f₁ hf₁df₂ hc₂ *
        (eichler hσ.invol F.f₁f₁ F.f₁g₂ hc₁)⁻¹ *
          (eichler hσ.invol F.f₁f₁ hf₁df₂ hc₂)⁻¹ = tv hσ.invol F.f₁f₁ ht
    rw [hkey]
    group
  rw [hg, htv, tv_smul]

end CFSG.LocalAnalysis.WeakClosure81.UOuter
