module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677Fstar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Glue
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_8F (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Setting16 D V₀ V L →
    barSub V₀ V hV L ≠ ⊥ → Conc4_136 D V₀ V hV L →
    (∀ L' : Subgroup G, Setting16 D V₀ V L' → barSub V₀ V hV L' ≠ ⊥ →
      Conc4_136 D V₀ V hV L' → ¬ Concl167F D V₀ V hV L') →
    ∃ L' : Subgroup G, Setting16 D V₀ V L' ∧ barSub V₀ V hV L' ≠ ⊥ ∧
      Conc4_136 D V₀ V hV L' ∧ Concl168 D V₀ V hV L'

@[expose] def R16_7F (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Setting16 D V₀ V L →
    barSub V₀ V hV L ≠ ⊥ → Conc4_136 D V₀ V hV L →
    ∃ L' : Subgroup G, Setting16 D V₀ V L' ∧ barSub V₀ V hV L' ≠ ⊥ ∧
      Conc4_136 D V₀ V hV L' ∧ Concl167F D V₀ V hV L'

theorem r16_8F_of_r16_8 {D : Data G} (h : R16_8 D) : R16_8F D :=
  fun V₀ V L hV hS hne hc hall =>
    h V₀ V L hV hS hne hc fun L' h1 h2 h3 h4 =>
      hall L' h1 h2 h3 (concl167F_of_concl167 D h1.hyp151 h2 h4)

theorem concl167_of_concl167F {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hn : ¬ Case167_7F D V₀ V hV) (h : Concl167F D V₀ V hV L) : Concl167 D V₀ V hV L := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact absurd h hn
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem r16_57_of_r16_57F {D : Data G} (h : R16_57F D) : R16_57 D :=
  fun V₀ V L hV hS h7 =>
    h V₀ V L hV hS (case167_7F_of_case167_7 D hS.setting.hyp151 hS.ne_bot h7)

theorem r16_7_of_r16_7F {D : Data G} (h57 : R16_57F D) (h : R16_7F D) : R16_7 D := by
  intro V₀ V L₀ hV hS₀ hne₀ hconc₀
  obtain ⟨L', h1, h2, h3, h4⟩ := h V₀ V L₀ hV hS₀ hne₀ hconc₀
  exact ⟨L', h1, h2, h3,
    concl167_of_concl167F (h57 V₀ V L₀ hV ⟨hS₀, hne₀, hconc₀⟩) h4⟩

theorem sixteen_seven2_of_steps_F (D : Data G) (h8 : R16_8F D) (h12 : R16_12 D)
    (h13 : R16_13_1 D) (h17 : R16_17 D) (h20 : R16_20 D) : R16_7F D := by
  intro V₀ V L₀ hV hS₀ hne₀ hconc₀
  by_contra hnot
  have hallF : ∀ L' : Subgroup G, Setting16 D V₀ V L' → barSub V₀ V hV L' ≠ ⊥ →
      Conc4_136 D V₀ V hV L' → ¬ Concl167F D V₀ V hV L' :=
    fun L' h1 h2 h3 h4 => hnot ⟨L', h1, h2, h3, h4⟩
  have hall : ∀ L' : Subgroup G, Setting16 D V₀ V L' → barSub V₀ V hV L' ≠ ⊥ →
      Conc4_136 D V₀ V hV L' → ¬ Concl167 D V₀ V hV L' :=
    fun L' h1 h2 h3 h4 => hallF L' h1 h2 h3 (concl167F_of_concl167 D h1.hyp151 h2 h4)
  obtain ⟨L₁, hS₁, hne₁, hconc₁, h168₁⟩ := h8 V₀ V L₀ hV hS₀ hne₀ hconc₀ hallF
  obtain ⟨L, hC, -⟩ := exists_counterex16_norm D hV hS₁ hne₁ hconc₁ h168₁ hall
  have hS : Setting16 D V₀ V L := hC.setting
  obtain ⟨-, h0, h1⟩ := h12 V₀ V L hV hC
  obtain ⟨⟨A, hA⟩, -⟩ := h13 V₀ V L hV hC
  obtain ⟨hAT, g, hAg, -⟩ := hA.1
  obtain ⟨Δ, hΔ⟩ := h17 V₀ V L hV hC A hA g hAg
  obtain ⟨B, U, hBU⟩ := sixteen_seven2_hyperplane_exists' D hS hV h0 h1 hA
  obtain ⟨h82, ⟨-, hfix⟩, hcard, hB2⟩ := h20 V₀ V L hV hC A g Δ hA hAg hΔ B U hBU
  obtain ⟨hncard, hIV, -, -, hirr, -⟩ := hΔ
  have hne' : ∃ I, I ∈ Δ := by
    by_contra hno
    have hempty : Δ = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => hno ⟨x, hx⟩
    rw [hempty] at hncard
    simp at hncard
  obtain ⟨I, hI⟩ := hne'
  have hP := hS.hyp16.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hBst : B ≤ stabTil V₀ V := hBU.1.trans (hAT.trans (D.sylowM.le.trans hMst))
  exact sixteen_seven2_final hV h0 (hIV I hI) hBst (hirr h82 I hI)
    (fun b hb => hfix b hb I hI) (hcard I hI) hB2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
