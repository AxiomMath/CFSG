module

public import CFSG.LocalAnalysis.StandardType.GGE0ExcAdjCore
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem ggE0ModelDataAt_E7
    (hS2 : ExcNoSuzukiReeAdj .E7) : GGE0ModelDataAt .E7 := by
  intro n f _hadm _hrank
  let C : Type := ↥(adjointGroup Tag.E7 (GaloisField 2 f))
  let e : (ggU .E7 n f).K ≃* C :=
    CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f)
  let I : Subgroup (MulAut C) := (MulAut.conj : C →* MulAut C).range
  have hcenterSrc : Subgroup.center (ggU .E7 n f).K = ⊥ :=
    CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot (K := GaloisField 2 f)
  refine ⟨C, inferInstance, e.toMonoidHom, I, e.surjective, ?_, ?_, le_rfl, ?_, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).2 e.injective, hcenterSrc]
  · have hmap := Subgroup.map_center_eq e
    rw [hcenterSrc, Subgroup.map_bot] at hmap
    exact hmap.symm
  · intro G _ ψ hker c _hcN hc
    have hker' : ψ.ker ≤ Subgroup.center (ggU .E7 n f).K := le_of_eq hker
    obtain ⟨g, hg, hz⟩ :=
      PsiDiag.Minu.exists_mem_centralizer_E7 (k := GaloisField 2 f) ψ hker' hc
    obtain ⟨u₀, hu₀⟩ := MonoidHom.mem_range.mp hg
    let u₁ : (ggU .E7 n f).K := u₀
    have hu₁ : ψ u₁ = g := hu₀
    rw [← hu₁] at hz
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, hker]
      exact hcenterSrc
    refine ⟨MulAut.conj ((e u₁)⁻¹), ⟨(e u₁)⁻¹, rfl⟩, ?_⟩
    intro u u' h
    have h1 : c * ψ u * c⁻¹ =
        (c * ψ u₁) * ψ (u₁⁻¹ * u * u₁) * (c * ψ u₁)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    have hmem : ψ (u₁⁻¹ * u * u₁) ∈ ψ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hz) _ hmem
    have h2 : (c * ψ u₁) * ψ (u₁⁻¹ * u * u₁) * (c * ψ u₁)⁻¹ =
        ψ (u₁⁻¹ * u * u₁) := by
      rw [hcomm.symm]; group
    have hψ : ψ u' = ψ (u₁⁻¹ * u * u₁) := by rw [← h, h1, h2]
    have hu' : u' = u₁⁻¹ * u * u₁ := hinj hψ
    rw [hu']
    simp [MulAut.conj_apply, map_mul, map_inv]
    exact inv_inv _
  · exact ggE0Model_adjointGroup (Or.inr (Or.inl rfl)) hS2 (GaloisField 2 f)

theorem ggE0At_E7
    (hS2 : ExcNoSuzukiReeAdj .E7) : GGE0At .E7 :=
  ggE0At_of_modelData (t := .E7) (ggE0InG1At_of_diagInner (t := .E7) ggPsiDiagInner_E7)
    (ggE0ModelDataAt_E7 hS2)

end CFSG.StandardType
