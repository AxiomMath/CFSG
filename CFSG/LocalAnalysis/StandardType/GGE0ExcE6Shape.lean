module

public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrameOn
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeConj
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextModel
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeModelG
public import CFSG.LocalAnalysis.StandardType.GGSteinbergCorrection

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem ggE0AtOn_E6_shape :
    GGE0AtOn .E6 (fun f p => p = 3 ∧ 3 ∣ 2 ^ f - 1) := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hR b hb hb1 m hm hEC C₀ hC₀
  obtain ⟨rfl, h3⟩ := hR
  have hm' : m⁻¹ ∈ ggM 3 B x L D J := Subgroup.inv_mem _ hm
  have hctx' := ggSixCtxV2_conj hctx m⁻¹
  have s1' := ggSixStepOne_conj s1 m⁻¹
  obtain ⟨Ω, hF, hA, h2, I, R, halg, hG1, hrig⟩ :=
    context_to_model hctx' s1' (Or.inl ⟨rfl, h3⟩)
  letI := hF
  letI := hA
  letI := h2
  have hG0 : ggG0 3 (B.map (MulAut.conj m⁻¹).toMonoidHom) (m⁻¹ * x * m⁻¹⁻¹)
      (L.map (MulAut.conj m⁻¹).toMonoidHom) (D.map (MulAut.conj m⁻¹).toMonoidHom)
      (J.map (MulAut.conj m⁻¹).toMonoidHom) = ggG0 3 B x L D J := by
    rw [ggG0_map_conj]
    exact map_conj_eq_of_mem_normalizer hm'
  have hG1eq := ggG1_comp_conj_eq hctx ggSteinbergCorrectionAt_E6 hm'
  have hmono : ∀ {G0 H K : Subgroup G}, H ≤ K → contextImage G0 H ≤ contextImage G0 K :=
    fun h => Subgroup.map_mono (Subgroup.comap_mono h)
  have hbG1 : b ∈ ggG1 ψ := ggBs_le_ggG1 hctx hb
  have hbI : contextImage (ggG0 3 (B.map (MulAut.conj m⁻¹).toMonoidHom) (m⁻¹ * x * m⁻¹⁻¹)
      (L.map (MulAut.conj m⁻¹).toMonoidHom) (D.map (MulAut.conj m⁻¹).toMonoidHom)
      (J.map (MulAut.conj m⁻¹).toMonoidHom)) (Subgroup.zpowers b) ≤ I := by
    refine (hmono ?_).trans hG1
    rw [hG1eq]
    exact Subgroup.zpowers_le.2 hbG1
  have hDle : D.map (MulAut.conj m⁻¹).toMonoidHom ≤
      ggG1 ((MulAut.conj m⁻¹).toMonoidHom.comp ψ) :=
    (Subgroup.map_mono (hctx.stdSub.1.1.trans hctx.bstar.1)).trans (ggBs_le_ggG1 hctx')
  have hEI := (hmono hDle).trans hG1
  refine ggE0Concl_of_modelShape s1'.1 halg R (b := b) ?_ hbI hb1 (hctx.bstar.2.1.2 b hb) ?_ hEI
    hEC hrig ?_
  · rw [hG0]
    exact hctx.bstar_le_normalizer hb
  · exact (Subgroup.map_mono (hctx.stdSub.1.1.trans hctx.bstar.1)).trans
      hctx'.bstar_le_normalizer
  · rw [hG0]
    exact hC₀

end CFSG.StandardType
