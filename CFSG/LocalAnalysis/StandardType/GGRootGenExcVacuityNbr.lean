module

public import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem l05nV5N_false (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (h : GGInnerDiagOnLabel GGRootGenExcNonHalfSplitLabel p Bs K) : False := by
  have hInnK : GGInnerDiagOn Bs K := hHyp.2.2.1.2 y K hnb
  have hHS := ggNbr_halfSplit_of_hyp hraw hiso hHyp.1 hnb hInnK
  obtain ⟨lab₂, hlab₂, hhas₂, R₂, _, I₂, F₂, θ₂, hHS₂⟩ := largeEvenMarking_exists_hasLabel hHS
  obtain ⟨lab₁, hlab₁, hhas₁, R₁, _, I₁, F₁, θ₁, hP₁⟩ := largeEvenMarking_exists_hasLabel h
  have hiso' : GGLabelIso lab₁ lab₂ := hRig lab₁ lab₂ (↥K ⧸ Subgroup.center ↥K) hlab₁ hlab₂
    hhas₁ hhas₂
  have heq : lab₂ = lab₁ := eq_of_ggLabelIso_of_excTag hP₁.1.1 hiso'
  exact hP₁.1.2.2 (largeEvenHalfSplit_false_of_excTag hP₁.1.1 (heq ▸ hHS₂))

theorem ggRootGenNbrInputOnQFour_of_notNonHalfSplit (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ GGRootGenExcNonHalfSplitLabel p lab)) :
    GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hK
  have hK' : GGInnerDiagOnLabel (fun p lab => GGRootGenExcNonHalfSplitLabel p lab ∨
      (GGRootGenOpenLabel p lab ∧ ¬ (X p lab ∨ GGRootGenExcNonHalfSplitLabel p lab))) p Bs K :=
    GGInnerDiagOnLabel.mono_label
      (S := fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab)
      (T := fun p lab => GGRootGenExcNonHalfSplitLabel p lab ∨
        (GGRootGenOpenLabel p lab ∧ ¬ (X p lab ∨ GGRootGenExcNonHalfSplitLabel p lab)))
      (fun lab hlab => (em (GGRootGenExcNonHalfSplitLabel p lab)).imp_right
        (fun hn => ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩)) hK
  rcases hK'.elim_or with h₁ | h₂
  · exact (l05nV5N_false hRig hraw hiso hHyp hnb h₁).elim
  · exact h G p B Bs x L D J hHyp hq hN y K hnb h₂

end CFSG.StandardType

end
