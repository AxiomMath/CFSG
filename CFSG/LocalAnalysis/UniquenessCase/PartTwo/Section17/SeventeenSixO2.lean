module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certificates

theorem delta_le_M_mem (D : Data G)
    (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    {H : Subgroup G} (hH : H ∈ Delta17_12 D 𝔉 r q L) : H ≤ D.M :=
  (le_iSup₂_of_le H hH le_rfl).trans
    (SeventeenSixteen.delta_le_M D 𝔉 V₀ V L r q hC)

@[expose] def Gap17_6_O2Rest (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  V₀ ≠ ⊥ → ¬ P17_12_1 r q L →
    ∀ H ∈ Delta17_12 D (fundPred q) r q L, ∀ g : G, g ∉ D.M →
      ¬ twoResidual H ≤ conjSubgroup D.M g

theorem o2Cond_of_gap (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : R17_7At D V₀ V L r q hC)
    (hGap : Gap17_6_O2Rest D V₀ V L r q hC) (hV₀ : V₀ ≠ ⊥) :
    ∀ H ∈ Delta17_12 D (fundPred q) r q L, ∀ g : G, g ∉ D.M →
      ¬ twoResidual H ≤ conjSubgroup D.M g := by
  intro H hH g hg
  by_cases h1 : P17_12_1 r q L
  · exact O2_case_one D (fundPred q) hC h1 h7 H hH g hg
  · exact hGap hV₀ h1 H hH g hg

section CertificatesTheorem

theorem seventeen_six_of_steps (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h7 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q), R17_7At D V₀ V L r q hC)
    (h15 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_15At D (fundPred q) V₀ V L r q hC)
    (h16 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_16At D (fundPred q) V₀ V L r q hC)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h117 : C117 D V₀ V)
    (hGap : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      Gap17_6_O2Rest D V₀ V L r q hC)
    (hK2 : CFSG.ComponentClassification.GS82PumpInputs.OddLieCharUnique) :
    R17_6At D V₀ V := by
  have hL2five : ∀ L ∈ calC D.M, ∀ r : ℕ, r ≠ 2 → IsChev (BarInf L) r →
      IsL2Over17 (BarInf L) 5 → Concl17_6 D L r :=
    fun L hL r hr hchev h5 => concl17_6_of_isL2Over17_five hK2 hL hr hchev h5
  have key : ∀ (L : Subgroup G) (r : ℕ), IsCounterexample17_6 D L r → False := by
    intro L r hc
    obtain ⟨L', r', q', hC'⟩ := exists_ctx17_6 hV hL2five hc
    by_cases hV₀ : V₀ = ⊥
    · exact seventeen_six_reductio_bot D V₀ V (fundPred q') hx h61 h126 h111 h7 h127
        L' r' q' hC' (h15 L' r' q' hC') hV₀
    · have hO2 : ∀ H ∈ Delta17_12 D (fundPred q') r' q' L', ∀ g : G, g ∉ D.M →
          ¬ twoResidual H ≤ conjSubgroup D.M g :=
        o2Cond_of_gap D hC' (h7 L' r' q' hC') (hGap L' r' q' hC') hV₀
      exact reductio_of_O2 D hx h61 h127 h1114 h162 hTor h1482 h126 (fundPred q') hC' hV₀
        (barSub_ne_bot_of_uniqueMax h127 hC'.hyp125 h117 hC'.memL (h7 L' r' q' hC').1)
        (h15 L' r' q' hC') (h16 L' r' q' hC') hO2
  refine ⟨?_, ?_, ?_⟩
  · intro L hL r hr hchev
    by_contra hnot
    exact key L r ⟨hL, hr, hchev, fun hconcl => hnot hconcl.1⟩
  · intro L hL r hr hchev h5
    by_contra hnot
    exact key L r ⟨hL, hr, hchev, fun hconcl => hnot (hconcl.2.1 h5)⟩
  · intro L hL r hr hchev h5
    by_contra hnot
    exact key L r ⟨hL, hr, hchev, fun hconcl => hnot (hconcl.2.2 h5)⟩

end CertificatesTheorem

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
