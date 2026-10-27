module

public import CFSG.LocalAnalysis.StandardType.GGTPAssembly
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTPTablePInput_of_leaves_onL (hTCJ : GGTCJKnown)
    (hP : GGNbrTablePNbrInputOnL GGRegimeB36L)
    (hRig : GGLabelRigidInput) (hM : GGE6DepModelKnown) (hNI : GGE6DepNonIsoPt)
    (hX : GGE6DepPerpXNotInL) (hLB : GGLBalanceInput) (hJL : GGTPJLayerInput) (hJS : GGTPJStabInput)
    (hN : GGTPClassicalExcl)
    : GGE6DepPerpTablePInput := by
  intro G _ _ p B Bs x L D J hcfg hop hinn hnt y K hnbr hE y' K' hnbr'
  obtain ⟨-, labJ, -, -, -, hlabJ, -, hhasJ⟩ := ggNbr_label_J_of_tcj hTCJ hcfg hnbr'
  obtain ⟨labK, hlabK, hhasK, -⟩ := largeEvenMarking_exists_hasLabel (hinn.2 y' K' hnbr')
  obtain ⟨-, -, -, lab₀, hlab₀, hmL, -⟩ := id hE
  obtain ⟨lab, hΛ₀, hhasL, R₀, -, I₀, F₀, θ₀, hlab_eq⟩ := largeEvenMarking_exists_hasLabel hmL
  rw [hlab_eq] at hΛ₀ hhasL
  have hReg : GGRegimeB36L p (Nat.card Bs) lab₀ labJ labK := by
    refine ⟨hE.1, hE.2.1, ?_⟩
    rcases hlab₀ with ⟨ht, -⟩ | ⟨ht, -⟩
    · exact Or.inl ht
    · exact Or.inr ht
  obtain ⟨labJ', labK', hJ', hK', hrow, hhJ', hhK'⟩ :=
    hP G p B Bs x L D J y' K' hcfg hinn.1 (hinn.2 y' K' hnbr') hnbr' lab₀ labJ labK hΛ₀ hlabJ
      hlabK hReg hhasL hhasJ hhasK
  exact ggTPTableRest_of_leaves hRig hM hNI hX hLB hJL hJS hN G p B Bs x L D J hcfg hop hinn hnt y K
    hnbr hE y' K' hnbr' labJ' labK' hJ' hK' hhJ' hhK' hrow

end CFSG.StandardType

end
