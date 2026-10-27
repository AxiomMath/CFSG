module

public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL364C4

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4.Res6L364 (K64 σ4 F4)

theorem conc_of_not_linear {F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K64))}
    (hF : CFSG.Open.IsElemAbelian 3 F)
    (hD : ∃ g ∈ F, Dhom K64 g ∉ linearAutGroup 3 K64) :
    Conc (CFSG.Open.StatedSL 3 K64) F := by
  obtain ⟨g, hg, hgD⟩ := hD
  obtain ⟨H, hH⟩ := exists_conj_slFieldSL_mem hF hg hgD
  set ψ : MulAut (CFSG.Open.StatedSL 3 K64) := (slConjSL K64 H)⁻¹ with hψ
  refine conc_of_conj ψ F ?_
  have hF1 : CFSG.Open.IsElemAbelian 3 (F.map (MulAut.conj ψ).toMonoidHom) :=
    CFSG.RankThree.PartTwo.Sec4.isElemAbelian_map _ hF
  have hf : slFieldSL K64 σ4 ∈ F.map (MulAut.conj ψ).toMonoidHom := by
    refine ⟨_, hH, ?_⟩
    simp [hψ, MulAut.conj_apply, mul_assoc]
  obtain ⟨e⟩ := exists_mulEquiv_fixedSub
  refine conc_of_fixedSub _ hF1 hf (fun F₀ hF₀ => ?_)
  refine conc_of_conc_map e.symm F₀ ?_
  exact ks1012AutHyp_sl34 (K := F4) card_F4_eq _
    (CFSG.RankThree.PartTwo.Sec4.isElemAbelian_map _ hF₀)

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
