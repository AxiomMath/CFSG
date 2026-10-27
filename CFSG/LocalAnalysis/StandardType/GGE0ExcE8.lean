module

public import CFSG.LocalAnalysis.StandardType.GGE0ExcAdjCore
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem ggE0ModelDataAt_E8
    (hS2 : ExcNoSuzukiReeAdj .E8) : GGE0ModelDataAt .E8 := by
  intro n f hadm hrank
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center (ggU .E8 n f).K = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)
  refine ⟨(ggU .E8 n f).K, inferInstance, MonoidHom.id _,
    (MulAut.conj : (ggU .E8 n f).K →* MulAut (ggU .E8 n f).K).range,
    Function.surjective_id, ?_, ?_, ?_, ?_, ?_⟩
  · exact MonoidHom.ker_id.trans hZ.symm
  · exact hZ
  · exact le_rfl
  · intro G _ ψ hψker c hcN hc
    obtain ⟨g, hg, hcg⟩ :=
      PsiDiag.Adj.exists_mem_centralizer_E8 (K := GaloisField 2 f) ψ hψker.le hc
    obtain ⟨u₀, rfl⟩ := (show ∃ u₀ : (ggU .E8 n f).K, ψ u₀ = g from hg)
    have hcg' : c * ψ u₀ ∈ Subgroup.centralizer (ψ.range : Set G) := hcg
    refine ⟨MulAut.conj u₀⁻¹, ⟨u₀⁻¹, rfl⟩, ?_⟩
    intro u u' hu
    have hinj : Function.Injective ψ :=
      (MonoidHom.ker_eq_bot_iff ψ).mp (hψker.trans hZ)
    have hzmem : c * ψ u * c⁻¹ ∈ ψ.range := ⟨u', hu.symm⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hcg') (c * ψ u * c⁻¹) hzmem
    have hgz : ψ u₀ * (c * ψ u * c⁻¹) * (ψ u₀)⁻¹ = ψ u := by
      have h2 : c⁻¹ * (c * ψ u * c⁻¹) * c =
          ψ u₀ * (c * ψ u * c⁻¹) * (ψ u₀)⁻¹ := by
        calc c⁻¹ * (c * ψ u * c⁻¹) * c
            = c⁻¹ * ((c * ψ u * c⁻¹) * (c * ψ u₀)) * (ψ u₀)⁻¹ := by group
          _ = c⁻¹ * ((c * ψ u₀) * (c * ψ u * c⁻¹)) * (ψ u₀)⁻¹ := by rw [hcomm]
          _ = ψ u₀ * (c * ψ u * c⁻¹) * (ψ u₀)⁻¹ := by group
      calc ψ u₀ * (c * ψ u * c⁻¹) * (ψ u₀)⁻¹
          = c⁻¹ * (c * ψ u * c⁻¹) * c := h2.symm
        _ = ψ u := by group
    have hz : c * ψ u * c⁻¹ = ψ (u₀⁻¹ * u * u₀) := by
      calc c * ψ u * c⁻¹
          = (ψ u₀)⁻¹ * (ψ u₀ * (c * ψ u * c⁻¹) * (ψ u₀)⁻¹) * ψ u₀ := by group
        _ = (ψ u₀)⁻¹ * ψ u * ψ u₀ := by rw [hgz]
        _ = ψ (u₀⁻¹ * u * u₀) := by simp only [map_mul, map_inv]
    have huu : u₀⁻¹ * u * u₀ = u' := hinj (hz.symm.trans hu)
    simpa only [MulAut.conj_apply, inv_inv, MonoidHom.id_apply] using huu
  · exact ggE0Model_adjointGroup (Or.inr (Or.inr rfl)) hS2 (GaloisField 2 f)

theorem ggE0At_E8
    (hS2 : ExcNoSuzukiReeAdj .E8) : GGE0At .E8 :=
  ggE0At_of_modelData (ggE0InG1At_of_diagInner ggPsiDiagInner_E8)
    (ggE0ModelDataAt_E8 hS2)

end CFSG.StandardType
