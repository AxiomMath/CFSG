module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDichHeis
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDichDih

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type} [Group G] [Finite G]

section Certified


theorem w15Eleven3Dich_holds : W15Eleven3Dich G := by
  intro M V₀ V U S H Q₀ p c
  obtain ⟨X, v, hX⟩ := Cfg1511.exists_xData c
  by_cases hall : ∀ A ∈ elemFamilyIn 2 (tSub15 M V₀ V U S), A ≤ qSub15 M V₀ V U H S
  · exact Or.inl hall
  · right
    obtain ⟨A, hA'⟩ := not_forall.1 hall
    obtain ⟨hA, hAQ⟩ := not_imp.1 hA'
    rcases c.card_X_eq_p_or_pow_three hX with h | h
    · exact c.s4Branch15_of_not_le hX h hA hAQ
    · exact absurd (c.forall_le_qSub15_of_card_X_eq_pow_three hX h A hA) hAQ

end Certified

end CFSG.LocalAnalysis.WeakClosure81
