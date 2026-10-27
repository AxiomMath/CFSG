module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResHeadsTwo
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3Eight

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section UnitaryEight

theorem ggFieldKLevel_u3Eight (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldClassicalResidualU3EightLabel p lab →
        LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  rintro p lab hp hp2 hlab ⟨ht, hl, rfl, hn⟩
  have hnot := ggFieldOther_twA_not (p := 3) ht
  exact largeEvenLabelAll_fieldKLevel_u3Eight ⟨ht, hl, hn⟩
    ((hpc 3 hp hp2 lab hlab hnot.1).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h)
    (hconj 3 hp hp2 lab hlab hnot.2) (hcen lab hlab) (hinn 3 hp hp2 lab hlab)

theorem ggNbrInnerWeylOn_of_u3Eight (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldClassicalResidualU3EightLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_u3Eight hpc hconj hcen hinn) hT

end UnitaryEight

section Head

theorem ggNbrInnerWeylOn_c9_of_nonClassical (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (h : GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab ∧ ¬ GGFieldFixD4Label p lab ∧
      ¬ (p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n) ∧ ¬ GGFieldClassicalTag lab) :
    GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab ∧ ¬ GGFieldFixD4Label p lab ∧
      ¬ (p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n) := by
  refine ggNbrInnerWeylOn_c9_of_nonClassicalU3Eight hL hPJ hG hpc hconj hcen hinn ?_
  refine ggNbrInnerWeylOn_of_u3Eight hL hPJ hG hpc hconj hcen hinn ?_
  refine h.mono fun p lab ⟨⟨hO, hFF, hFN, hFD, hG2, hres⟩, hu⟩ => ⟨hO, hFF, hFN, hFD, hG2, ?_⟩
  rcases hres with hnc | hres
  · exact hnc
  · exact absurd hres hu

end Head

end CFSG.StandardType

end
