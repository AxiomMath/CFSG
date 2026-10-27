module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggFieldKLevel_of_fixKnownRow {r : ℕ} (hr : 3 ≤ r) {S Rw : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab →
      p ∣ lab.n ∧ Rw p lab ∧ Rw p ⟨lab.tag, lab.rank, lab.n / p⟩)
    (hΛ : ∀ p lab, LargeEvenInLambda2 lab → S p lab →
      LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩)
    (hNot : ∀ p lab, Rw p lab → GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3))
    (hFix : GGFieldFixKnown S)
    (hRow : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      Rw p lab → LargeEvenLabelAll lab (GGNbrWeylRowPlain p r))
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab hSl
  obtain ⟨hdvd, hrow, hrow₀⟩ := hS p lab hSl
  have hR : LargeEvenLabelAll lab (GGNbrWeylRowPlain p r) := hRow p lab hp hp2 hlab hrow
  have hR₀ : LargeEvenLabelAll ⟨lab.tag, lab.rank, lab.n / p⟩ (GGNbrWeylRowPlain p r) :=
    hRow p _ hp hp2 (hΛ p lab hlab hSl) hrow₀
  have hRK : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r) :=
    hR.mono fun _ _ _ _ ⟨hi, hl, hn⟩ =>
      ⟨hi, hl, fun hs hna => ggTorusNoLineComp_of_ggTorusNoLine (hn hs hna)⟩
  have hCyc : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
    (hpc p hp hp2 lab hlab (hNot p lab hrow).1).mono fun _ _ _ _ h =>
      ggRawFieldCycW_of_pCyclic h
  have hAll := largeEvenLabelAll_and (hconj p hp hp2 lab hlab (hNot p lab hrow).2)
    (largeEvenLabelAll_and (hcen lab hlab) (largeEvenLabelAll_and (hinn p hp hp2 lab hlab)
      (hFix p lab hp hp2 hlab hSl)))
  have hFx : LargeEvenLabelAll lab (GGRawFieldFix p ⟨lab.tag, lab.rank, lab.n / p⟩) :=
    (largeEvenLabelAll_and hCyc hAll).mono fun _ _ _ _ ⟨hcy, hc, hce, hi, hst⟩ hs hna =>
      ggRawFieldFix_of_std hc (ggRawFieldNorm_of_central hce hi hs hna) hcy hst hs hna
  exact largeEvenLabelAll_fieldKLevelComp_of_fix hp hr hRK hR₀ hCyc hFx

end CFSG.StandardType

end
