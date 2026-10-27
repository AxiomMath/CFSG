module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalBlock
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Aut
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.Blueprint Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem kL34Data_holds :
    ∀ (X : Type) [Group X] [Finite X], IsL3 X 2 →
      Nat.card X = 2 ^ 6 * 3 ^ 2 * 5 * 7 ∧
        Nat.card (MulAut X) = 2 ^ 8 * 3 ^ 3 * 5 * 7 ∧
          pRank 5 (⊤ : Subgroup X) = 1 ∧
            ∀ (Y : Type) [Group Y] [Finite Y],
              (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
                Nonempty (Y ≃* ↥(StatedSL 3 K))) →
                pRank 3 (⊤ : Subgroup Y) = 2 := by
  intro X _ _ hL3
  have hclass : CFSG.Open.StatedClassicalModel X .PSL 3 2 2 :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide : StatedLieTag.PSL ∈ classicalTags)).1 hL3
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hclass
  letI := hKfield
  letI := hKfin
  have hcardX : Nat.card X = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := 3) (by norm_num)]
    rw [hKcard]
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    simp only [h4]
    have hprod : (∏ x ∈ Finset.Icc 2 3, (4 ^ x - 1)) = 945 := by decide
    rw [hprod]
    norm_num
  refine ⟨hcardX, ?_, ?_, ?_⟩
  ·
    have hAutX : Nat.card (MulAut X) =
        Nat.card (MulAut (projectiveSL 3 K)) := by
      refine Nat.card_congr (MulAut.congr ?_).toEquiv
      exact e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K).symm
    rw [hAutX]
    have := CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut (k := K) hKcard
    norm_num at this ⊢
    exact this
  ·
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num)
      (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h5dvd : 5 ∣ Nat.card X := by rw [hcardX]; norm_num
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
    have hpos : 1 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) :=
      CFSG.ClassicalGroups.SLnThreeLocal.one_le_pRank_of_orderOf (H := ⊤) (x := x)
        (Subgroup.mem_top x) hx
    have hle : CFSG.Open.pRank 5 (⊤ : Subgroup X) ≤ (Nat.card X).factorization 5 :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.pRank_top_le_factorization
        (p := 5) (by norm_num)
    rw [hcardX] at hle
    have hfac : ((2 ^ 6 * 3 ^ 2 * 5 * 7 : ℕ)).factorization 5 = 1 := by
      have h5not : ¬ 5 ∣ (2 ^ 6 * 3 ^ 2 * 7 : ℕ) := by norm_num
      have hmul : (2 ^ 6 * 3 ^ 2 * 5 * 7 : ℕ) = 5 * (2 ^ 6 * 3 ^ 2 * 7) := by ring
      rw [Nat.factorization_def _ (by norm_num : Nat.Prime 5), hmul,
        padicValNat.mul (p := 5) (a := 5) (b := 2 ^ 6 * 3 ^ 2 * 7)
          (by norm_num) (by norm_num),
        padicValNat.eq_zero_of_not_dvd h5not, padicValNat_self, Nat.add_zero]
    rw [hfac] at hle
    omega
  ·
    intro Y _ _ ⟨K', hK'field, hK'fin, hK'card, ⟨eY⟩⟩
    letI := hK'field
    letI := hK'fin
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 3 K')) = 2 :=
      CFSG.Quasithin.R3c.pRank_three_statedSL_three_even (K := K') (n := 2) (by norm_num)
        (by rw [hK'card]; norm_num)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
      (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y)]
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 3 K')) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eY
    exact h1.trans h2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
