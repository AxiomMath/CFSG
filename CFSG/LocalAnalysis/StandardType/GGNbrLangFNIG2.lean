module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIExcUntw
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem kgFieldRestrictionOn_g2 : KGFieldRestrictionOn (kgfniRow .g2) := by
  intro p lab hp hp2 hlab _ht3 hrow
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨htag, _hdvd⟩ := hrow
  simp only [KGFNIFamily.tagCase] at htag
  subst htag
  dsimp only [LargeEvenInLambda2] at hlab
  exact kgFieldRestrictionOn_of_excUntw_model (τ := .G2) (n := n)
    (lab := ⟨LargeEvenLieTag.G2, r, n⟩) hp hp2 (Or.inl rfl) hlab.2.2 hlab rfl rfl

end CFSG.StandardType

end
