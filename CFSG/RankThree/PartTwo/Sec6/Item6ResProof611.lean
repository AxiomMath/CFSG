module

public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.KFacts.KS6OuterIndex
public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec6.Item612UsedOf

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

@[expose] def Item6_11_1Main : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c → False

namespace Res611

variable {G : Type} [Group G] [Finite G]

theorem eq_zpowers_of_isCyclic {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hBA : B ≤ A) (hB : IsCyclic B) {c : G} (hcB : c ∈ B) (hc1 : c ≠ 1) :
    B = Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.2 c (hBA hcB)) hc1
  obtain ⟨g, hg⟩ := hB.exists_generator
  have hcard : Nat.card B = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hA.2 (g : G) (hBA g.2))
  have hle : Nat.card B ≤ 3 := by
    rw [hcard]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcB)
    (by rw [Nat.card_zpowers, hc3]; exact hle)).symm

end Res611

open Res611

theorem item6_11_1_of (h641 : Item6_4_1) (h66 : Item6_6) (h612 : Item6_12)
    (hM : Item6_11_1Main) : Item6_11_1 := by
  intro G _ _ hG A hA
  by_contra hlt
  push Not at hlt
  have hAE : A ∉ partTwoE G := fun hAE => by
    have := (Late.isE27_of_mem_partTwoE hAE).pRank_eq
    omega
  have hS : A ∈ partTwoS G :=
    hG.toTheoremFourHyp.partTwoF_diff_partTwoE_subset ⟨hA, hAE⟩
  obtain ⟨-, -, E, hE, hEA⟩ := hA
  obtain ⟨U, hU⟩ := h641 G hG E hE
  obtain ⟨c, hcE, hc1, L, hL, -⟩ := h612 G hG A hS E ⟨hE, hEA⟩ U hU
  have hcA : c ∈ A := hEA hcE
  have hLc : L ∈ thetaComponentsAt 3 c := hL.1
  have hLs : L ∈ lStar A := hL.2.2
  have hcyc := h66 G hG A hS L hLs
  have hcC : c ∈ A ⊓ thetaQuotCentralizer L :=
    ⟨hcA, mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc⟩
  have heq : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c :=
    eq_zpowers_of_isCyclic hS.1.1 inf_le_left hcyc hcC hc1
  exact hM G hG A hS hlt c hcA hc1 L hL heq

theorem item6_11_1_of_used (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) (h641 : Item6_4_1) (hM : Item6_11_1Main) : Item6_11_1 :=
  item6_11_1_of h641 (rank3II_6_6_of_used h45 h48 h49) (rank3II_6_12_of_used h45 h48 h49 hKf) hM

end CFSG.RankThree.PartTwo.Sec6
