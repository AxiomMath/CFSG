module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Model
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section E6

theorem ggFieldFixKnown_E6 :
    GGFieldFixKnown GGFieldFixE6Label := by
  intro p lab hp hp2 hlab hS
  obtain ⟨⟨-, hF, hrow⟩, ht⟩ := hS
  have hp3 : p ≠ 3 := by
    rcases hrow with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · rcases h with h | h | h <;> rw [ht] at h <;> cases h
    · rcases h with h | h <;> rw [ht] at h <;> cases h
    · rw [ht] at h; cases h
    · rw [ht] at h; cases h
    · rw [ht] at h; cases h
    · exact h
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht hF
  subst ht
  exact recipeChevalley_and (fun K _ _ hK _ _ f hf hord =>
    e6_fixStd hn hK hp hp2 hp3 hF hf hord) hQ

end E6

end CFSG.StandardType

end
