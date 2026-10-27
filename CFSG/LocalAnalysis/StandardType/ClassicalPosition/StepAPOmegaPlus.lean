module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaPlus
public import CFSG.LieType.Universal.Spin.Datum

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

private lemma sAOp_spinMatrix_injective (F : Type) [Field F] [CharP F 2] (n : ℕ) :
    Function.Injective (Spin.spinMatrix (Spin.quadPlus n F)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero F 2)

theorem spin_pow_eq_one_of_conj_POmegaPlus {F : Type} [Field F] [CharP F 2] {n : ℕ} (hn : 3 ≤ n)
    {X : Type} [Group X] (ψ : spinGroup (Spin.quadPlus n F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n F)))
    {d : X} {p : ℕ} (hdp : d ^ p = 1)
    {s₀ : spinGroup (Spin.quadPlus n F)}
    (hconj : ∀ u, d⁻¹ * ψ u * d = ψ (s₀ * u * s₀⁻¹)) :
    s₀ ^ p = 1 := by
  have hinj := sAOp_spinMatrix_injective F n
  have hsl : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ
      (Spin.spinMatrix (Spin.quadPlus n F) s₀) d := by
    intro u
    exact ⟨s₀ * u * s₀⁻¹, by simp only [map_mul, map_inv], hconj u⟩
  have hslp : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ
      (Spin.spinMatrix (Spin.quadPlus n F) (s₀ ^ p)) 1 := by
    have h := hsl.pow p
    rw [hdp, ← map_pow] at h
    exact h
  apply conj_eq_unique_POmegaPlus n F hn ψ hψ (s' := 1)
  intro u
  obtain ⟨u', hu'j, hu'ψ⟩ := hslp u
  have h : u' = (s₀ ^ p) * u * (s₀ ^ p)⁻¹ :=
    hinj (by rw [hu'j]; simp only [map_mul, map_inv])
  rw [h] at hu'ψ
  simpa using hu'ψ.symm

end CFSG.StandardType.ClassicalPosition
