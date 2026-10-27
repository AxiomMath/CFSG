module

public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.StandardType.GGFFModelBasis
import CFSG.LocalAnalysis.StandardType.GGFFModelN
import CFSG.LocalAnalysis.StandardType.GGFFModelSL
import CFSG.LocalAnalysis.StandardType.GGFFModelSLN
import CFSG.Adapters.StatedSLTwoField

@[expose] public section

namespace CFSG.StandardType.FF81

open CFSG.Open (StatedClassicalModel)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

theorem modelN_of_model {L : Type} [Group L] {n : ℕ} (hn : n = 5 ∨ n = 6)
    (hL : StatedClassicalModel L .PSL (n + 1) 2 1) {z : Fin 3 → L} (hz : GGFF.Model L z) :
    GGFF.ModelN L z := by
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hL
  have key : ∀ z' : Fin 3 → L, GGFF.Model L z' → GGFF.ModelN L z' → GGFF.ModelN L z := by
    intro z' hz' hN'
    obtain ⟨g, hg⟩ := hz.torus (GGFF.tor z') hz'.isElemAbelian_tor' hz'.card_tor'
    have hv : ∀ v, vecElt (fun i => g * z i * g⁻¹) v = g * vecElt z v * g⁻¹ := fun v =>
      GGFF.vecElt_map (MulAut.conj g) z v
    have htor : ∀ x : L, (∃ v, x = vecElt (fun i => g * z i * g⁻¹) v) ↔
        ∃ v, x = vecElt z' v := fun x => by
      rw [← hz'.mem_tor', hg x]
      simp only [hv]
    obtain ⟨k, hk⟩ := (hz.conj g).exists_conj_of_tor_eq hz' htor
    have hz_eq : z = fun i => (g⁻¹ * k) * z' i * (g⁻¹ * k)⁻¹ := by
      funext i
      have := hk i
      calc z i = g⁻¹ * (g * z i * g⁻¹) * g := by group
        _ = g⁻¹ * (k * z' i * k⁻¹) * g := by rw [this]
        _ = (g⁻¹ * k) * z' i * (g⁻¹ * k)⁻¹ := by group
    rw [hz_eq]
    exact hN'.conj _
  rcases hn with rfl | rfl
  · exact key _ (GGFF.model_SL6.ofMulEquiv e.symm) (GGFF.modelN_SL6.ofMulEquiv e.symm)
  · exact key _ (GGFF.model_SL7.ofMulEquiv e.symm) (GGFF.modelN_SL7.ofMulEquiv e.symm)

end CFSG.StandardType.FF81

end
