module

public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley


theorem largeEvenLabelAll_inndiag_e6 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .E6 ∨ lab.tag = .twE6) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  intro Q hQ
  rcases h with h | h <;> dsimp only at h <;> subst h
  · exact recipeChevalley_inndiag (fun K _ _ _ => InndiagE6.ggInndiagNormal_E6 K) hQ
  · exact recipeTwisted_and (P := LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I)
      (fun K _ _ hK _ _ => InndiagE6.ggInndiagNormal_twE6 hn K hK) hQ

theorem ggInndiagNormalOtherInput_holds : GGInndiagNormalOtherInput := by
  intro lab hlab hnot
  obtain ⟨t, l, n⟩ := lab
  cases t with
  | A => exact absurd (Or.inr (Or.inl rfl)) hnot
  | twA => exact largeEvenLabelAll_inndiag_unitary hlab (Or.inl rfl)
  | B => exact absurd (Or.inl (Or.inl rfl)) hnot
  | C => exact absurd (Or.inl (Or.inr (Or.inl rfl))) hnot
  | D =>
    by_cases hl : l = 3
    · exact absurd (Or.inr (Or.inr (Or.inl ⟨rfl, hl⟩))) hnot
    · exact absurd (Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, hl⟩)))) hnot
  | twD =>
    by_cases hl2 : l = 2
    · exact absurd (Or.inr (Or.inr (Or.inr ⟨rfl, hl2⟩))) hnot
    by_cases hl3 : l = 3
    · exact largeEvenLabelAll_inndiag_unitary hlab (Or.inr ⟨rfl, hl3⟩)
    · exact absurd (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hl2, hl3⟩))))) hnot
  | E6 => exact largeEvenLabelAll_inndiag_e6 hlab (Or.inl rfl)
  | twE6 => exact largeEvenLabelAll_inndiag_e6 hlab (Or.inr rfl)
  | twB2 => exact absurd (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hnot
  | G2 => exact largeEvenLabelAll_inndiag_exc hlab (by simp [GGInndiagExcLabel])
  | F4 => exact largeEvenLabelAll_inndiag_exc hlab (by simp [GGInndiagExcLabel])
  | E7 => exact largeEvenLabelAll_inndiag_exc hlab (by simp [GGInndiagExcLabel])
  | E8 => exact largeEvenLabelAll_inndiag_exc hlab (by simp [GGInndiagExcLabel])
  | triD4 => exact largeEvenLabelAll_inndiag_exc hlab (by simp [GGInndiagExcLabel])
  | twF4 => exact largeEvenLabelAll_inndiag_exc hlab (by simp [GGInndiagExcLabel])
  | G2der => exact largeEvenLabelAll_inndiag_exc hlab (by simp [GGInndiagExcLabel])
  | twF4der => exact largeEvenLabelAll_inndiag_exc hlab (by simp [GGInndiagExcLabel])
  | B2der => exact largeEvenLabelAll_inndiag_exc hlab (by simp [GGInndiagExcLabel])

theorem ggInndiagNormalInput_holds : GGInndiagNormalInput :=
  ggInndiagNormalInput_of_other ggInndiagNormalOtherInput_holds

end CFSG.StandardType
