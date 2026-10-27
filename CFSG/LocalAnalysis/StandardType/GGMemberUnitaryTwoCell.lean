module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1UnitaryTwo
public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrX

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

theorem ggInnerDiagOnLabel_rank_five_of_not_rank_three {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G}
    (hno : ¬ GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3) p Bs X)
    (h : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) p Bs X) :
    GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X := by
  have hsplit : GGInnerDiagOnLabel
      (fun p lab => ((ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) ∧
          ¬ (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3)) ∨
        (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3)) p Bs X :=
    h.mono_label (fun lab hs => by
      by_cases h3 : ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3
      · exact Or.inr h3
      · exact Or.inl ⟨hs, h3⟩)
  rcases hsplit.elim_or with h5 | h3
  · refine h5.mono_label (fun lab hlab => ?_)
    obtain ⟨⟨hESU, hn, hr⟩, hnot⟩ := hlab
    refine ⟨hESU, hn, ?_⟩
    rcases hr with h3 | h5
    · exact absurd ⟨hESU, hn, h3⟩ hnot
    · exact h5
  · exact absurd h3 hno

theorem ggMember_unitaryTwoCell_rank_five
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ X ∈ 𝒦)
    (h : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) p Bs X) :
    GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X := by
  rcases hX with hXL | hX
  · subst hXL
    exact ggInnerDiagOnLabel_rank_five_of_not_rank_three
      (fun h3 => not_ggInnerDiagOnLabel_unitary_four hcfg.1.1
        (h3.mono_label (fun lab hlab => by
          obtain ⟨hESU, -, hr3⟩ := hlab
          rcases hESU.1 with ⟨ht, -⟩ | ⟨ht, -⟩
          · exact ⟨Or.inl ht, hr3, hESU.2⟩
          · exact ⟨Or.inr ht, hr3, hESU.2⟩)))
      h
  · obtain ⟨y, hy⟩ := hcfg.2.2.2.1.2 X hX
    exact ggInnerDiagOnLabel_rank_five_of_not_rank_three
      (not_ggInnerDiagOnLabel_unitary_four_two_of_ggNbr hLB hP hcfg hy) h

end CFSG.StandardType

end
