module

public import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem l05nV5L_false (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (h : GGInnerDiagOnLabel GGRootGenExcNonSplitLabel p Bs L) : False := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨lab₂, hlab₂, hhas₂, R₂, _, I₂, F₂, θ₂, hP₂⟩ :=
    largeEvenMarking_exists_hasLabel hst.1
  obtain ⟨lab₁, hlab₁, hhas₁, R₁, _, I₁, F₁, θ₁, hP₁⟩ :=
    largeEvenMarking_exists_hasLabel h
  have hiso : GGLabelIso lab₁ lab₂ :=
    hRig lab₁ lab₂ (↥L ⧸ Subgroup.center ↥L) hlab₁ hlab₂ hhas₁ hhas₂
  have heq : lab₂ = lab₁ := eq_of_ggLabelIso_of_excTag hP₁.1.1 hiso
  exact hP₁.1.2.2 (heq ▸ hP₂.1)

theorem ggRootGenLInputOnQFour_of_notNonSplit (hRig : GGLabelRigidInput)
    {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ GGRootGenExcNonSplitLabel p lab)) :
    GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  have hsplit : GGInnerDiagOnLabel (fun p lab => GGRootGenExcNonSplitLabel p lab ∨
      (GGRootGenOpenLabel p lab ∧ ¬ (X p lab ∨ GGRootGenExcNonSplitLabel p lab))) p Bs L :=
    GGInnerDiagOnLabel.mono_label
      (fun lab hlab => (em (GGRootGenExcNonSplitLabel p lab)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩) hL
  rcases hsplit.elim_or with h₁ | h₂
  · exact (l05nV5L_false hRig hHyp h₁).elim
  · exact h G p B Bs x L D J hHyp hq hN h₂

end CFSG.StandardType

end
