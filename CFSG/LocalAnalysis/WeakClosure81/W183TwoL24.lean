module

public import CFSG.LocalAnalysis.WeakClosure81.W183FourDefs
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoL24Pure
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoL24Big
public import CFSG.LocalAnalysis.WeakClosure81.W18ASCtx
public import CFSG.LocalAnalysis.WeakClosure81.W18Tail

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section Certified


theorem tail1812TwoL24U34_of_inputs (h210 : Asch2_10) (h4 : Tail1812FourL24U34 G) :
    Tail1812TwoL24U34 G := by
  intro h162 h172 h5_4 h5_11 h5_12 h5_13 D V₀ V H i c h2 hK hL g hgT hgK hgi hA
  obtain ⟨L, hLc, hLT, hQ⟩ := hL
  have x : Ctx188 D V₀ V H i 3 := c.ctx188_three_AS h162 h5_11 h2
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
  have hN : calNIn H D.T = {H ⊓ D.M} := c.calNIn_eq_AS h5_11 h5_13
  by_cases hbig : ∃ g' : G, Gam183 V H (eOmegaZ H D.T) i g' ∧
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g')
  · obtain ⟨g'', hg''T, hg''K, hg''i, hg''3⟩ := x.w183tp_big_member_le_T M hK hbig
    exact h4 h162 h172 h5_4 h5_11 h5_12 h5_13 c h2 hK ⟨L, hLc, hLT, hQ⟩ hg''T hg''K hg''i hg''3
  · have hall : ∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
        (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g') = 2 := by
      intro g' hg'
      have hg'K : ¬ vInH V H g' ≤ kerMV V H := fun hle => hg'.2 (hle.trans hK)
      rcases c.relIndex_cases hg'K with h2' | h3'
      · exact h2'
      · exact absurd ⟨g', hg', h3'⟩ hbig
    exact x.w183tp_false_pure h210 c h2 M hN hK hLc hLT hQ hall hgT hgK hgi hA

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
