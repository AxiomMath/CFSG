module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveThin
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Shape

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def ThinShape (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, IsL2 X n) ∨ (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd X q) ∨ IsJ1 X

theorem three_dvd_card_bar2 {L : Subgroup G} (h : CFSG.Open.pRank 3 L = 1) :
    3 ∣ Nat.card (Bar2 L) := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (⊤ : Subgroup (Bar2 L))
  rw [pRank_bar2_eq_of_odd (Y := L) Nat.prime_three (by norm_num), h, pow_one] at hE
  rw [← hE]
  exact Subgroup.card_subgroup_dvd_card E

theorem isCyclic_sylow_of_thin8 {L : Subgroup G} (h : F08.Thin8 L) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (P : Sylow p (Bar2 L)) : IsCyclic ↥(P : Subgroup (Bar2 L)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one hp2
    ((pRank_bar2_eq_of_odd hp hp2).le.trans (h p hp hp2)) P

theorem isCyclic_of_isPGroup_of_thin8 {L : Subgroup G} (h : F08.Thin8 L) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B : Subgroup (Bar2 L)} (hB : IsPGroup p B) : IsCyclic ↥B := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hBS⟩ := hB.exists_le_sylow
  haveI := isCyclic_sylow_of_thin8 h hp hp2 S
  exact Subgroup.isCyclic_of_le hBS

theorem center_eq_bot_of_thin8 {M L : Subgroup G} (hL : L ∈ calC M) (h : F08.Thin8 L) :
    center (Bar2 L) = ⊥ :=
  center_bar2_eq_bot_of_isCyclic_sylow hL fun _ hp hp2 P => isCyclic_sylow_of_thin8 h hp hp2 P

theorem thinShape_of_thin8 (D : Data G) (hKThin : KThinSimple) {L : Subgroup G}
    (hL : L ∈ calC D.M) (h : F08.Thin8 L) (h3 : 3 ∣ Nat.card (Bar2 L)) : ThinShape (Bar2 L) := by
  rcases bar2_shape_of_isCyclic_sylow D hL hKThin
    (fun _ hp hp2 P => isCyclic_sylow_of_thin8 h hp hp2 P) with h2 | ⟨n, hSz⟩ | h2 | h2
  · exact Or.inl h2
  · exact absurd h3
      (CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz)
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h2)

theorem isCyclic_of_isPGroup_of_pRank_eq_one {L : Subgroup G} (h : CFSG.Open.pRank 3 L = 1)
    {B : Subgroup G} (hBL : B ≤ L) (hB : IsPGroup 3 B) : IsCyclic ↥B :=
  CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) hBL hB
    (((CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥L).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L).symm).trans_le h.le)

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Shape

end
