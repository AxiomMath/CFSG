module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIExcUntw
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem kgFieldRestrictionOn_f4 : KGFieldRestrictionOn (kgfniRow .f4) := by
  intro p lab hp hp2 hlab _ht3 hrow
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨htag, hdvd⟩ := hrow
  simp only [KGFNIFamily.tagCase] at htag
  subst htag
  have hn : 2 ≤ n := hp.two_le.trans (Nat.le_of_dvd hlab.1 hdvd)
  exact kgFieldRestrictionOn_of_excUntw_model (τ := .F4) (n := n)
    (lab := ⟨LargeEvenLieTag.F4, r, n⟩) hp hp2 (Or.inr (Or.inl rfl)) hn hlab rfl rfl

end CFSG.StandardType

end
