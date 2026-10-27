module

public import CFSG.Milestones.ASVolI.F4L3Aut

public section

namespace CFSG.ASVolI

section Model

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {F : Type} [Field F] [CharP F 2] {E : Type} [Group E]
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)}

theorem burnsideF429a_L3_mem_range_of_cent (hΦ : Function.Injective Φ)
    (hρ : Function.Injective ρ)
    (hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹)
    (hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F) {b : E}
    (hc : ∀ p ∈ projUnitriangular 3 F, b * Φ p = Φ p * b) : b ∈ Φ.range := by
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.mp (hE b)
  have hx : ∀ a : F, (conjAut 3 F A * fieldAut 3 F σ) (xP a) = xP a := by
    intro a
    rw [← hAσ]
    exact (burnsideF447_comm_iff hΦ hΦρ b _).mpr
      (hc _ (mem_Ubar.mpr ⟨0, a, 0, by rw [wP_zero, yP_zero]; group⟩))
  have hy : ∀ a : F, (conjAut 3 F A * fieldAut 3 F σ) (yP a) = yP a := by
    intro a
    rw [← hAσ]
    exact (burnsideF447_comm_iff hΦ hΦρ b _).mpr
      (hc _ (mem_Ubar.mpr ⟨0, 0, a, by rw [wP_zero, xP_zero]; group⟩))
  obtain ⟨hσ, c, hcA⟩ := burnsideF447_fix_xy A σ hx hy
  refine ⟨wP c, ?_⟩
  apply hρ
  rw [hAσ, hσ, map_one, mul_one, hcA, burnsideF447_rho_Phi hΦ hΦρ]

end Model

section Main

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34

theorem burnsideF429a_ctr_L3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : 2 ≤ f) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : ctr T ≤ Gp := by
  intro z hz
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨F, hFf, hFfin, hFchar, Φ, ρ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hρ, hΦρ, hE, hD, hO,
    h₁, h₂, -⟩ := burnsideF447_setup hf hyp.toHypF_4_4g
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hNp := burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂
  have hUT : pCoreOf 2 (M₁ ⊓ M₂) ≤ T :=
    CFSG.QuasithinUnique.IsSylowTwoOf.le_of_normalizes hT
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  rw [hNp.2] at hUT
  have hc : ∀ p ∈ projUnitriangular 3 F, z * Φ p = Φ p * z := fun p hp =>
    (Subgroup.mem_centralizer_iff.mp hz.2 (Φ p) (hUT ⟨p, hp, rfl⟩)).symm
  rw [← hrange]
  exact burnsideF429a_L3_mem_range_of_cent hΦ hρ hΦρ hE hc

end Main

end CFSG.ASVolI
