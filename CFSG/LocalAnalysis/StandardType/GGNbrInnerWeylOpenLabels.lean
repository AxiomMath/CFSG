module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMore
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylIrredLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTypeA
public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGNbrInnerWeylOn.mono_of_lambda {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S' p lab → S p lab)
    (h : GGNbrInnerWeylOn S) : GGNbrInnerWeylOn S' := by
  intro G _ _ p B Bs x L D J hC y K hK hN hxK P hP
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hC.1.2.2.2.2.2.1.2.1
  obtain ⟨hKt, lab, hlab, hraw⟩ := h G p B Bs x L D J hC y K hK hN hxK P hP
  refine ⟨hKt, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hPθ, hQ⟩
  exact ⟨hs, hna, θ, hPθ, fun hS' => hQ (hS p lab hp hp2 hlab hS')⟩

theorem largeEvenLabelAll_weylInnerKLevel_of_noLine_or {p : ℕ} {lab : LargeEvenLabel}
    (hPow : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
    (hT : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∃ r, (GGTorusLift p r R ∨ r = 0) ∧ GGTorusNoLine p r R I) :
    LargeEvenLabelAll lab (GGNbrWeylInnerKLevel p) := fun Q hQ =>
  largeEvenRawDatum_mono (fun _ _ _ _ ⟨hq, h1, h2⟩ =>
    ⟨hq, fun hs hna => ⟨h1 hs hna, h2 hs hna⟩⟩) (largeEvenLabelAll_and hPow hT Q hQ)

@[expose] def GGNbrWeylUnitDvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧
    p ∣ lab.rank + 1 ∧ ¬ (lab.rank = 5 ∧ p = 3)

@[expose] def GGNbrWeylUnitSixThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrWeylUnitThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ lab.tag = .twA ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGNbrWeylUnitFiveLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGNbrWeylInnerOpenLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylRest12Label p lab ∧ GGNbrPowMemLabel p lab ∧ ¬ GGNbrNsVacLabel p lab ∧
    ¬ GGNbrWeylInnerIrredLabel p lab ∧ ¬ GGNbrWeylInnerTypeALabel p lab

@[expose] def GGNbrWeylInnerExcLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylInnerOpenLabel p lab ∧ ¬ GGNbrWeylUnitDvdLabel p lab ∧
    ¬ GGNbrWeylUnitThreeLabel p lab ∧ ¬ GGNbrWeylUnitFiveLabel p lab ∧
    ¬ GGNbrWeylUnitSixThreeLabel p lab

@[expose] def GGNbrWeylE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ lab.tag = .E6 ∧
    ((p = 3 ∧ p ∣ 2 ^ lab.n - 1) ∨ (lab.n = 1 ∧ (p = 3 ∨ p = 7)))

@[expose] def GGNbrWeylTwE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ lab.tag = .twE6 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)

@[expose] def GGNbrWeylExcPlusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧
    p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrWeylTwF4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ lab.tag = .twF4 ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrWeylFieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylRest12Label p lab ∧ ¬ GGNbrPowMemLabel p lab ∧ ¬ GGNbrNsVacLabel p lab

theorem ggNbrWeylRest12Label_cover (p : ℕ) (lab : LargeEvenLabel)
    (h : GGNbrWeylRest12Label p lab) :
    GGNbrNsVacLabel p lab ∨ GGNbrWeylFieldLabel p lab ∨ GGNbrWeylInnerIrredLabel p lab ∨
      GGNbrWeylInnerTypeALabel p lab ∨ GGNbrWeylUnitDvdLabel p lab ∨
      GGNbrWeylUnitThreeLabel p lab ∨ GGNbrWeylUnitFiveLabel p lab ∨
      GGNbrWeylUnitSixThreeLabel p lab ∨ GGNbrWeylInnerExcLabel p lab := by
  by_cases hv : GGNbrNsVacLabel p lab
  · exact Or.inl hv
  by_cases hpm : GGNbrPowMemLabel p lab
  · by_cases hi : GGNbrWeylInnerIrredLabel p lab
    · exact Or.inr (Or.inr (Or.inl hi))
    by_cases ha : GGNbrWeylInnerTypeALabel p lab
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    have hopen : GGNbrWeylInnerOpenLabel p lab := ⟨h, hpm, hv, hi, ha⟩
    by_cases h1 : GGNbrWeylUnitDvdLabel p lab
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    by_cases h2 : GGNbrWeylUnitThreeLabel p lab
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2)))))
    by_cases h3 : GGNbrWeylUnitFiveLabel p lab
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))))
    by_cases h4 : GGNbrWeylUnitSixThreeLabel p lab
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4)))))))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hopen, h1, h2, h3, h4⟩)))))))
  · exact Or.inr (Or.inl ⟨h, hpm, hv⟩)

end CFSG.StandardType

end
