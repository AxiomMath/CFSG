module

public import CFSG.LocalAnalysis.StandardType.GGE0ExcAdjCore
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem ggE0ModelDataAt_F4
    (hS2 : ExcNoSuzukiReeAdj .F4) : GGE0ModelDataAt .F4 := by
  intro n f hadm hrank
  have hcenterU : Subgroup.center (ggU .F4 n f).K = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  refine ⟨(ggU .F4 n f).K, inferInstance, MonoidHom.id (ggU .F4 n f).K,
    (MulAut.conj : (ggU .F4 n f).K →* MulAut (ggU .F4 n f).K).range,
    Function.surjective_id, ?_, hcenterU, le_rfl, ?_, ?_⟩
  · rw [MonoidHom.ker_id]
    exact hcenterU.symm
  · intro G _ ψ hker c hcN hc
    have hker' : ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) := hker.le
    obtain ⟨g, hg, hz⟩ :=
      PsiDiag.Adj.exists_mem_centralizer_F4 (K := GaloisField 2 f) ψ hker' hc
    have hg' : g ∈ ψ.range := hg
    obtain ⟨u₀, hu₀⟩ := MonoidHom.mem_range.mp hg'
    rw [← hu₀] at hz
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, hker]
      exact hcenterU
    refine ⟨MulAut.conj u₀⁻¹, ⟨u₀⁻¹, rfl⟩, ?_⟩
    intro u u' h
    have h1 : c * ψ u * c⁻¹ =
        (c * ψ u₀) * ψ (u₀⁻¹ * u * u₀) * (c * ψ u₀)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    have hmem : ψ (u₀⁻¹ * u * u₀) ∈ ψ.range :=
      MonoidHom.mem_range.mpr ⟨u₀⁻¹ * u * u₀, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hz) _ hmem
    have h2 : (c * ψ u₀) * ψ (u₀⁻¹ * u * u₀) * (c * ψ u₀)⁻¹ =
        ψ (u₀⁻¹ * u * u₀) := by
      rw [hcomm.symm]
      group
    have hψ : ψ u' = ψ (u₀⁻¹ * u * u₀) := by rw [← h, h1, h2]
    have hu' : u' = u₀⁻¹ * u * u₀ := hinj hψ
    rw [hu']
    simp only [MonoidHom.id_apply, MulAut.conj_apply, inv_inv]
  · exact ggE0Model_adjointGroup (Or.inl rfl) hS2 (GaloisField 2 f)

theorem ggE0At_F4
    (hS2 : ExcNoSuzukiReeAdj .F4) : GGE0At .F4 := by
  exact ggE0At_of_modelData (ggE0InG1At_of_diagInner ggPsiDiagInner_F4)
    (ggE0ModelDataAt_F4 hS2)

end CFSG.StandardType
