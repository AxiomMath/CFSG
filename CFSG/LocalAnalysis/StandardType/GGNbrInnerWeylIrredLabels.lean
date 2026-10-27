module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestVac
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreSp
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreOrth
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreExc
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenUnitaryIrred
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTorusNoLine_of_ggTorusIrredSC {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : CorFourTwoOpen.GGTorusIrredSC p R I) : GGTorusNoLine p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3 hsc
  obtain ⟨W, hW1, hW2, -, -⟩ := h L' ψ hψ hker hperf A hA hAI h3 hsc
  exact ⟨W, hW1, fun _ a₀ ha₀ ha₁ => ggNbrExists_move_of_irred hp hA h3 hW2 ha₀ ha₁⟩

theorem largeEvenLabelAll_weylInnerKLevel_of_irred {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hPow : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
    (hT : LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusIrred p r R I) :
    LargeEvenLabelAll lab (GGNbrWeylInnerKLevel p) :=
  (largeEvenLabelAll_and hPow hT).mono fun _ _ _ _ ⟨h1, r, hl, hT'⟩ hs hna =>
    ⟨h1 hs hna, r, Or.inl hl, ggTorusNoLine_of_ggTorusIrred hp hT'⟩

theorem largeEvenLabelAll_weylInnerKLevel_of_irredSC {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime)
    (hPow : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
    (hT : LargeEvenLabelAll lab fun R _ I _ => CorFourTwoOpen.GGTorusIrredSC p R I) :
    LargeEvenLabelAll lab (GGNbrWeylInnerKLevel p) :=
  (largeEvenLabelAll_and hPow hT).mono fun _ _ _ _ ⟨h1, hT'⟩ hs hna =>
    ⟨h1 hs hna, 0, Or.inr rfl, ggTorusNoLine_of_ggTorusIrredSC hp hT'⟩

@[expose] def GGNbrWeylInnerIrredLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧
    (GGReflSpLabel p lab ∨ GGSpNonsplitLabel p lab ∨ GGCorFourTwoOrthSplitLabel p lab ∨
      GGOrthNsLabel p lab ∨ GGTableBNbrInnerExcSplitLabel p lab ∨ GGTableBF4Label p lab ∨
      GGUnitaryCoprimeLabel p lab)

section Main

theorem ggNbrInnerWeylOn_innerIrred : GGNbrInnerWeylOn GGNbrWeylInnerIrredLabel :=
  ggNbrInnerWeylOn_of_labels fun p lab hp hp2 hlab ⟨hpow, h⟩ => by
    have hPow := largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow
    rcases h with h | h | h | h | h | h | h
    · exact largeEvenLabelAll_weylInnerKLevel_of_irred hp hPow
        ((SpModel.largeEvenLabelAll_weylInputs_symplectic hp hlab h).mono
          fun _ _ _ _ ⟨r, hl, _, hT, _⟩ => ⟨r, hl, hT⟩)
    · exact largeEvenLabelAll_weylInnerKLevel_of_irredSC hp hPow
        (largeEvenLabelAll_torusIrredSC_spNonsplit hp hlab h)
    · exact largeEvenLabelAll_weylInnerKLevel_of_irred hp hPow
        (largeEvenLabelAll_torusIrred_orthSplit hp hlab h)
    · exact largeEvenLabelAll_weylInnerKLevel_of_irredSC hp hPow
        (largeEvenLabelAll_torusIrredSC_orthNs hp h)
    · exact largeEvenLabelAll_weylInnerKLevel_of_irred hp hPow
        (largeEvenLabelAll_torusIrred_excSplit hp hlab h)
    · exact largeEvenLabelAll_weylInnerKLevel_of_irred hp hPow
        (largeEvenLabelAll_torusIrred_F4 hp hlab h)
    · exact largeEvenLabelAll_weylInnerKLevel_of_irredSC hp hPow
        (largeEvenLabelAll_torusIrredSC_unitary hp hlab h)

end Main

end CFSG.StandardType

end
