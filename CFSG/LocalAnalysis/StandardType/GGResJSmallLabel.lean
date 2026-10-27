module

public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
import CFSG.LocalAnalysis.StandardType.GGNbrU63StepTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def ggResJPRankTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRootGenSmallRankLabel p lab ∨ lab.tag = .G2 ∨ lab.tag = .G2der ∨ lab.tag = .twF4der ∨
    (lab.tag = .triD4 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) ∨
    (lab.tag = .twF4 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1))

theorem GGResHyp.innerDiag_J_pRank_ge_three_of_card_gamma {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (hJ : GGInnerDiagOnLabel S p Bs J) :
    StandardType.LargeEvenMarking ↥J (fun lab R _ I _ _ => S p lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  refine largeEvenMarking_mono ?_ hJ
  rintro lab R _ I _ θ ⟨hSl, hN, hInd⟩
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  refine ⟨hSl, (ggBeta J θ hN).range, ?_, isElemAbelian_range_ggBeta θ hBs hN, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact ggBeta_mem J θ hN hInd b
  · rw [NbrU63.card_range_ggBeta_eq hJperf θ hN]
    exact h3

section PRankTwo

theorem GGResHyp.false_of_innerDiag_J_pRankTwo_of_card_gamma {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (hJ : GGInnerDiagOnLabel ggResJPRankTwoLabel p Bs J) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  rcases hJ.elim_or with h | h
  · exact not_largeEvenMarking_smallRank hp hp2
      (hH.innerDiag_J_pRank_ge_three_of_card_gamma h3 h)
  rcases h.elim_or with h | h
  · exact ggInndiag_pRank_le_two_G2 hp hp2 (hH.innerDiag_J_pRank_ge_three_of_card_gamma h3 h)
  rcases h.elim_or with h | h
  · exact ggInndiag_pRank_le_two_G2der hp hp2
      (hH.innerDiag_J_pRank_ge_three_of_card_gamma h3 h)
  rcases h.elim_or with h | h
  · exact ggInndiag_pRank_le_two_twF4der hp hp2
      (hH.innerDiag_J_pRank_ge_three_of_card_gamma h3 h)
  rcases h.elim_or with h | h
  · exact ggInndiag_pRank_le_two_triD4 hp (hH.innerDiag_J_pRank_ge_three_of_card_gamma h3 h)
  · exact ggInndiag_pRank_le_two_twF4 hp hp2
      (hH.innerDiag_J_pRank_ge_three_of_card_gamma h3 h)

end PRankTwo

end CFSG.StandardType

end
