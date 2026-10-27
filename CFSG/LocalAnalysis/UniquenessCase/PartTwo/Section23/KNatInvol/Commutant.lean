module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.LineTorus
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatInvol

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem addCommutantScalar_of_sylowFixedLine {Γ : Subgroup (GL ι K)} {e₀ : ι → K}
    (hline : KTabC.SylowFixedLine Γ e₀) (htorus : AutZC.LineTorus Γ e₀)
    (hspan : Submodule.span K
      (Set.range fun γ : ↥Γ => ((γ : GL ι K) : Matrix ι ι K) *ᵥ e₀) = ⊤) :
    CFSG.RankThree.GF2n.Stroth80.AddCommutantScalar Γ := by
  unfold CFSG.RankThree.GF2n.Stroth80.AddCommutantScalar
  intro f hf
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥Γ))
  obtain ⟨x, hx⟩ := hline S
  let w₀ : ι → K := ((x : GL ι K) : Matrix ι ι K) *ᵥ e₀
  have hfixw : ∀ s ∈ (S : Subgroup ↥Γ), ((s : GL ι K) : Matrix ι ι K) *ᵥ w₀ = w₀ :=
    fun s hs => (hx w₀).2 ⟨1, by rw [one_smul]⟩ s hs
  have hfixfw : ∀ s ∈ (S : Subgroup ↥Γ),
      ((s : GL ι K) : Matrix ι ι K) *ᵥ f w₀ = f w₀ := by
    intro s hs
    rw [← hf ((s : GL ι K)) s.2 w₀, hfixw s hs]
  obtain ⟨a, ha⟩ := (hx (f w₀)).1 hfixfw
  have hstep : ∀ (γ : ↥Γ) (c : K),
      f (c • (((γ : GL ι K) : Matrix ι ι K) *ᵥ e₀)) =
        a • (c • (((γ : GL ι K) : Matrix ι ι K) *ᵥ e₀)) := by
    intro γ c
    by_cases hc : c = 0
    · rw [hc]
      simp
    · obtain ⟨t, htΓ, ht⟩ := htorus (Units.mk0 c hc)
      let y : ↥Γ := γ * ⟨t, htΓ⟩ * x⁻¹
      have hyeq : ((y : GL ι K) : Matrix ι ι K)
          = ((γ : GL ι K) : Matrix ι ι K) * ((t : GL ι K) : Matrix ι ι K) *
            ((x⁻¹ : GL ι K) : Matrix ι ι K) := by
        simp only [y, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
      have hx'x : ((x⁻¹ : GL ι K) : Matrix ι ι K) * ((x : GL ι K) : Matrix ι ι K) = 1 := by
        simp only [← Units.val_mul, ← Subgroup.coe_mul Γ x⁻¹ x, inv_mul_cancel, Subgroup.coe_one,
          Units.val_one]
      have hx'w : ((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w₀ = e₀ := by
        calc ((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w₀
            = ((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ
                (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀) := rfl
          _ = (((x⁻¹ : GL ι K) : Matrix ι ι K) * ((x : GL ι K) : Matrix ι ι K)) *ᵥ e₀ := by
                rw [Matrix.mulVec_mulVec]
          _ = e₀ := by rw [hx'x, Matrix.one_mulVec]
      have hy : ((y : GL ι K) : Matrix ι ι K) *ᵥ w₀
          = c • (((γ : GL ι K) : Matrix ι ι K) *ᵥ e₀) := by
        calc ((y : GL ι K) : Matrix ι ι K) *ᵥ w₀
            = (((γ : GL ι K) : Matrix ι ι K) * ((t : GL ι K) : Matrix ι ι K) *
                ((x⁻¹ : GL ι K) : Matrix ι ι K)) *ᵥ w₀ := by rw [hyeq]
          _ = (((γ : GL ι K) : Matrix ι ι K) * ((t : GL ι K) : Matrix ι ι K)) *ᵥ
                (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w₀) := by rw [← Matrix.mulVec_mulVec]
          _ = ((γ : GL ι K) : Matrix ι ι K) *ᵥ
                (((t : GL ι K) : Matrix ι ι K) *ᵥ
                  (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w₀)) := by
                rw [← Matrix.mulVec_mulVec]
          _ = ((γ : GL ι K) : Matrix ι ι K) *ᵥ (((t : GL ι K) : Matrix ι ι K) *ᵥ e₀) := by
                rw [hx'w]
          _ = ((γ : GL ι K) : Matrix ι ι K) *ᵥ (c • e₀) := by rw [ht, Units.val_mk0]
          _ = c • (((γ : GL ι K) : Matrix ι ι K) *ᵥ e₀) := by rw [Matrix.mulVec_smul]
      rw [← hy, hf ((y : GL ι K)) y.2 w₀, ha, Matrix.mulVec_smul]
  have htop : ∀ v : ι → K, ∀ b : K, f (b • v) = a • (b • v) := by
    intro v
    have hv : v ∈ Submodule.span K
        (Set.range fun γ : ↥Γ => ((γ : GL ι K) : Matrix ι ι K) *ᵥ e₀) := by
      rw [hspan]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun v _ => ∀ b : K, f (b • v) = a • (b • v))
      ?_ ?_ ?_ ?_ hv
    · rintro v ⟨γ, rfl⟩ b
      exact hstep γ b
    · intro b
      simp
    · intro u v _ _ hu hv b
      calc f (b • (u + v)) = f (b • u + b • v) := by rw [smul_add]
        _ = f (b • u) + f (b • v) := by rw [map_add]
        _ = a • (b • u) + a • (b • v) := by rw [hu b, hv b]
        _ = a • (b • (u + v)) := by rw [smul_add, smul_add]
    · intro c u _ hu b
      rw [smul_smul]
      exact hu (b * c)
  refine ⟨a, fun v => ?_⟩
  simpa using htop v 1

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatInvol
