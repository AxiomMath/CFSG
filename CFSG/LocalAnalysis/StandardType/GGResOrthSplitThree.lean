module

public import CFSG.LocalAnalysis.StandardType.GGResTwoCells
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
import CFSG.LocalAnalysis.StandardType.GGPSUFourRankSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGInnerDiagOnLabel.settled_of_splitDThree {G : Type} [Group G] {p : ℕ}
    {Bs L : Subgroup G}
    (h : GGInnerDiagOnLabel (fun p lab => lab.tag = .D ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1)
      p Bs L) :
    GGInnerDiagOnLabel ggTwoSettledLabelL p Bs L := by
  obtain ⟨hperf, ⟨tag, rank, n⟩, hlab, hraw⟩ := h
  obtain ⟨_R, _, _I, _F, _, _, _θ, ⟨htag, hrank, hpn⟩, _⟩ := largeEvenRawDatum_exists hraw
  dsimp only at htag hrank hpn
  subst htag hrank
  have hlabA : LargeEvenInLambda2 ⟨.A, 3, n⟩ :=
    show 1 ≤ n ∧ 1 ≤ 3 ∧ (3 = 1 → 2 ≤ n) from ⟨hlab.1, by norm_num, by norm_num⟩
  obtain ⟨F, _, _, hF, hs, hna, θ, -, hrest⟩ := hraw
  exact ⟨hperf, ⟨.A, 3, n⟩, hlabA, F, inferInstance, inferInstance, hF, hs, hna, θ,
    Or.inr (Or.inl ⟨rfl, hpn⟩), hrest⟩

theorem GGResHyp.false_of_L_twDThree_split {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel (fun p lab => lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1)
      p Bs L) :
    False := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨-, ⟨tag, rank, n⟩, hlab, hraw⟩ := ggInnerDiagOnLabel_L_pRank_ge_three hH.1 hM
  obtain ⟨_R, _, _I, _F, _, _, _θ, ⟨htag, hrank, hpn⟩, _⟩ := largeEvenRawDatum_exists hraw
  dsimp only at htag hrank hpn
  subst htag hrank
  obtain ⟨F, _, _, hF, -, -, -, -, E, hEI, hE, h3⟩ := hraw
  exact absurd (h3.trans (card_le_sq_of_subset_matConj_GU_four hlab.1 hF hp hp2 hpn hE hEI))
    (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))

theorem ggResMultiNodeRestTwoCellInput_dThree_split :
    GGResMultiNodeRestTwoCellInput (fun p lab =>
      lab.tag = .D ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) := by
  intro G _ _ p B Bs x L D J y K hH _ hF hSt hE ⟨_, hnL, _, hM, _⟩
  exact (hnL hM.settled_of_splitDThree).elim

theorem ggResMultiNodeRestTwoCellInput_twDThree_split :
    GGResMultiNodeRestTwoCellInput (fun p lab =>
      lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) := by
  apply GGResMultiNodeRestTwoCellInput.of_false
  intro G _ _ p _ B Bs x L D J y K hH hM _
  exact hH.false_of_L_twDThree_split hM

theorem ggResMultiNodeRestTwoCellInput_orthSplit_three :
    GGResMultiNodeRestTwoCellInput (fun p lab =>
      (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) :=
  (ggResMultiNodeRestTwoCellInput_dThree_split.or
    ggResMultiNodeRestTwoCellInput_twDThree_split).mono fun _ _ ⟨htag, hrank, hpn⟩ =>
      htag.imp (fun h => ⟨h, hrank, hpn⟩) fun h => ⟨h, hrank, hpn⟩

end CFSG.StandardType

end
