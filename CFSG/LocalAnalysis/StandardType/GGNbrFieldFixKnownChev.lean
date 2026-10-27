module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevRecipe
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Chev

theorem ggFieldFixKnown_chev : GGFieldFixKnown GGFieldFixChevLabel := by
  intro p lab hp _ hlab hS
  obtain ⟨-, ht⟩ := hS
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  rcases ht with ht | ht | ht <;> dsimp only at ht <;> subst ht
  · exact recipeChevalley_and (fun K _ _ hK _ _ f hf hord =>
      chev_fixStd (τ := .F4) (Or.inl rfl) hn hK hp.pos hf hord) hQ
  · exact recipeChevalley_and (fun K _ _ hK _ _ f hf hord =>
      chev_fixStd (τ := .E7) (Or.inr (Or.inl rfl)) hn hK hp.pos hf hord) hQ
  · exact recipeChevalley_and (fun K _ _ hK _ _ f hf hord =>
      chev_fixStd (τ := .E8) (Or.inr (Or.inr rfl)) hn hK hp.pos hf hord) hQ

end Chev

end CFSG.StandardType

end
