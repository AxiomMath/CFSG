module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentralizerPort
public import CFSG.LocalAnalysis.StandardType.GGXInLDispatch

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly

theorem labelOn_of_label {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    (h : GGInnerDiagOnLabel GGLabQTwo p Bs L) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ lab.n = 1 ∧
      ∀ S : LargeEvenLabel → Prop, S lab → labelOn S p Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨-, -, -, -, -, -, -, hQ2, -, -⟩ := largeEvenRawDatum_exists hraw
  have hn : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hQ2
    omega
  refine ⟨lab, hlab, hn, fun S hSlab => ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩⟩
  rintro R' _ I' F' ⟨hs, hna, θ', hq, hrest⟩
  exact ⟨hs, hna, θ', ⟨hq, hSlab⟩, hrest⟩

theorem toralInput_of_families
    (hSl : slTwoInput) (hPsu5 : psuAtLeastFiveTwoInput) (hSp : spTwoTransportInput)
    (hOm : omegaTwoTransportInput) (hE7 : eSevenTwoInput) (hE8 : eEightTwoInput)
    (hTE6 : twistedESixTwoInput) (hF4 : f4TwoInput) (hE6 : e6TwoInput)
    (hPsu4 : psuFourTwoInput) (hSm : smallLabelsTwoInput) : toralInput := by
  intro G _ _ p B Bs x L D J hS R _ θ hN
  obtain ⟨⟨tag, rank, n⟩, hlab, hn, key⟩ := labelOn_of_label hS.2.1
  have hn' : n = 1 := hn
  cases tag
  case A => exact hSl G p B Bs x L D J hS (key _ (Or.inl rfl)) R θ hN
  case twA =>
    have hlam : 1 ≤ n ∧ 2 ≤ rank ∧ (rank = 2 → 2 ≤ n) := hlab
    by_cases h3 : rank = 3
    · exact hPsu4 G p B Bs x L D J hS (key _ (Or.inl ⟨rfl, h3⟩)) R θ hN
    · have h4 : 4 ≤ rank := by
        obtain ⟨-, h2, h2'⟩ := hlam
        by_contra hlt
        have h22 := h2' (by omega)
        omega
      exact (hPsu5 G p B Bs x L D J hS (key _ ⟨rfl, h4⟩) R θ hN).1
  case B => exact hSp G p B Bs x L D J hS (key _ (Or.inl rfl)) R θ hN
  case C => exact hSp G p B Bs x L D J hS (key _ (Or.inr rfl)) R θ hN
  case D =>
    obtain ⟨-, h3'⟩ : 1 ≤ n ∧ 3 ≤ rank := hlab
    by_cases h3 : rank = 3
    · exact hSl G p B Bs x L D J hS (key _ (Or.inr ⟨rfl, h3⟩)) R θ hN
    · have h4 : 4 ≤ rank := by omega
      exact hOm G p B Bs x L D J hS (key _ (Or.inl ⟨rfl, h4⟩)) R θ hN
  case twD =>
    obtain ⟨-, h2'⟩ : 1 ≤ n ∧ 2 ≤ rank := hlab
    by_cases h2 : rank = 2
    · exact hSm G p B Bs x L D J hS (key _ (by simp [h2])) R θ hN
    · by_cases h3 : rank = 3
      · exact hPsu4 G p B Bs x L D J hS (key _ (Or.inr ⟨rfl, h3⟩)) R θ hN
      · have h4 : 4 ≤ rank := by omega
        exact hOm G p B Bs x L D J hS (key _ (Or.inr ⟨rfl, h4⟩)) R θ hN
  case E6 => exact hE6 G p B Bs x L D J hS (key _ rfl) R θ hN
  case E7 => exact hE7 G p B Bs x L D J hS (key _ rfl) R θ hN
  case E8 => exact hE8 G p B Bs x L D J hS (key _ rfl) R θ hN
  case F4 => exact hF4 G p B Bs x L D J hS (key _ rfl) R θ hN
  case twE6 => exact (hTE6 G p B Bs x L D J hS (key _ rfl) R θ hN).1
  case triD4 => exact hSm G p B Bs x L D J hS (key _ (by simp)) R θ hN
  case G2 => exact hSm G p B Bs x L D J hS (key _ (by simp)) R θ hN
  case twB2 => exact hSm G p B Bs x L D J hS (key _ (by simp)) R θ hN
  case twF4 => exact hSm G p B Bs x L D J hS (key _ (by simp)) R θ hN
  case B2der => exact hSm G p B Bs x L D J hS (key _ (by simp)) R θ hN
  case G2der => exact hSm G p B Bs x L D J hS (key _ (by simp)) R θ hN
  case twF4der => exact hSm G p B Bs x L D J hS (key _ (by simp)) R θ hN

theorem internalInput_of_families
    (hPsu5 : psuAtLeastFiveTwoInput) (hTE6 : twistedESixTwoInput) : internalInput := by
  intro G _ _ p B Bs x L D J hS R _ θ hN hxL
  obtain ⟨-, h | h⟩ := GGXInL.lup8g_dispatch_label hS hxL
  · exact (hPsu5 G p B Bs x L D J hS h.2 R θ hN).2 hxL
  · exact (hTE6 G p B Bs x L D J hS h R θ hN).2 hxL

theorem ggQTwoCentralizerInput_of_families
    (hExt : externalTransfer) (hInt : internalTransfer)
    (hSl : slTwoInput) (hPsu5 : psuAtLeastFiveTwoInput) (hSp : spTwoTransportInput)
    (hOm : omegaTwoTransportInput) (hE7 : eSevenTwoInput) (hE8 : eEightTwoInput)
    (hTE6 : twistedESixTwoInput) (hF4 : f4TwoInput) (hE6 : e6TwoInput)
    (hPsu4 : psuFourTwoInput) (hSm : smallLabelsTwoInput) : GGQTwoCentralizerInput :=
  assemble hExt hInt
    ⟨toralInput_of_families hSl hPsu5 hSp hOm hE7 hE8 hTE6 hF4 hE6 hPsu4 hSm,
      internalInput_of_families hPsu5 hTE6⟩

end CFSG.StandardType.GGQ2CentPort

end
