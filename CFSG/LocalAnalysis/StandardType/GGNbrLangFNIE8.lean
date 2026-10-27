module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIExcUntw
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem kgFieldRestrictionOn_e8 : KGFieldRestrictionOn (kgfniRow .e8) := by
  intro p lab hp hp2 hlab _ht3 hrow
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨htag, hdvd⟩ := hrow
  simp only [KGFNIFamily.tagCase] at htag
  subst htag
  dsimp only [LargeEvenInLambda2] at hlab
  exact kgFieldRestrictionOn_of_excUntw_model (τ := .E8) (n := n)
    (lab := ⟨LargeEvenLieTag.E8, r, n⟩) hp hp2 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (le_trans hp.two_le (Nat.le_of_dvd hlab.1 hdvd)) hlab rfl rfl

end CFSG.StandardType

end
