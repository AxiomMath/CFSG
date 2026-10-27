module

public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestExc
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestClassical
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestE6
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestExcl
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggInndiagCommRestInput_holds :
    GGInndiagCommRestInput := by
  intro lab hlab hX hP
  obtain ⟨t, l, n⟩ := lab
  have hlab' := hlab
  obtain ⟨hn, hl⟩ := hlab
  cases t with
  | A =>
    have h2 : ¬ 2 ≤ l := fun h => hP (Or.inl (Or.inl ⟨rfl, h⟩))
    have h1 : 1 ≤ l := hl.1
    exact largeEvenLabelAll_inndiagComm_linearTwo hlab' (Or.inl ⟨rfl, show l = 1 by omega⟩)
  | twA => exact absurd (Or.inr (Or.inl (Or.inl rfl))) hP
  | B =>
    have h3 : ¬ 3 ≤ l := fun h => hP (Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, h⟩)))
    have h2 : 2 ≤ l := hl.1
    exact largeEvenLabelAll_inndiagComm_symplecticTwo hlab' ⟨Or.inl rfl, show l = 2 by omega⟩
  | C =>
    have h3 : ¬ 3 ≤ l := fun h => hP (Or.inr (Or.inr (Or.inr ⟨Or.inr rfl, h⟩)))
    have h2 : 2 ≤ l := hl.1
    exact largeEvenLabelAll_inndiagComm_symplecticTwo hlab' ⟨Or.inr rfl, show l = 2 by omega⟩
  | D =>
    have h3 : l ≠ 3 := fun h => hP (Or.inl (Or.inr ⟨rfl, h⟩))
    have h4 : l ≠ 4 := fun h => hX (Or.inl ⟨rfl, h⟩)
    have hl3 : 3 ≤ l := hl
    exact largeEvenLabelAll_inndiagComm_omegaPlus hlab' rfl (show 5 ≤ l by omega)
  | twD =>
    have h3 : l ≠ 3 := fun h => hP (Or.inr (Or.inl (Or.inr ⟨rfl, h⟩)))
    have hl2 : 2 ≤ l := hl
    rcases Nat.lt_or_ge l 4 with h | h
    · exact largeEvenLabelAll_inndiagComm_linearTwo hlab' (Or.inr ⟨rfl, show l = 2 by omega⟩)
    · exact largeEvenLabelAll_inndiagComm_omegaMinus hlab' rfl h
  | E6 => exact largeEvenLabelAll_inndiagComm_E6 rfl
  | E7 => exact absurd (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))) hP
  | E8 => exact absurd (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr rfl)))))) hP
  | F4 => exact absurd (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl rfl))))) hP
  | twE6 => exact largeEvenLabelAll_inndiagComm_twE6 hlab' rfl
  | triD4 => exact largeEvenLabelAll_inndiagComm_triD4 hlab' rfl
  | G2 => exact absurd (Or.inr (Or.inr (Or.inl (Or.inl rfl)))) hP
  | twB2 => exact largeEvenLabelAll_inndiagComm_twB2 hlab' rfl
  | twF4 => exact largeEvenLabelAll_inndiagComm_twF4 hlab' rfl
  | B2der => exact absurd (Or.inr rfl) hX
  | G2der => exact largeEvenLabelAll_inndiagComm_g2der hlab' rfl
  | twF4der => exact largeEvenLabelAll_inndiagComm_twF4der hlab' rfl

theorem ggRawInndiagIsoRound5_of_noIso
    (hN : GGExclNoIsoInput) :
    GGRawInndiagIsoRound5 :=
  ⟨ggInndiagCommRestInput_holds, ggRawInndiagIsoExclInput_of_noIso hN⟩

end CFSG.StandardType

end
