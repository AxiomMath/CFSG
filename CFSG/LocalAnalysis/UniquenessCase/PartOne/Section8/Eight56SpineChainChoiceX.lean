module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56SpineChainFusion
import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

theorem exists_choiceX_of_controlsFusion {G : Type} [Group G] [Finite G] (D : Data G)
    {L Q P : Subgroup G} (hcex : Cex856 D L Q P) (hfus : ControlsFusionIn D.M P) :
    ∃ X : Subgroup G, ChoiceX D L Q P X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hno
  have hC : ∀ x ∈ P, orderOf x = 3 → centralizer ({x} : Set G) ≤ D.M := by
    intro x hxP hxord
    by_contra hxnot
    refine hno ⟨Subgroup.zpowers x, hcex, Subgroup.zpowers_le.2 hxP, ?_, ?_⟩
    · rw [Nat.card_zpowers, hxord]
    · have hcent : centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
          centralizer ({x} : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      rw [hcent]
      exact hxnot
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hcex.mem.1
  have hr : 1 ≤ CFSG.Open.pRank 3 L := by rw [hcex.rank]; norm_num
  have hPne : P ≠ ⊥ := sylow_three_ne_bot_of_one_le_pRank hLM hr hcex.sylowP
  have h3dvd : 3 ∣ Nat.card P :=
    hcex.sylowP.isPGroup.card_eq_or_dvd.resolve_left fun h1 =>
      hPne (Subgroup.card_eq_one.mp h1)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 h3dvd
  have hyP : (y : G) ∈ P := y.2
  have hyord : orderOf (y : G) = 3 := (Subgroup.orderOf_coe y).trans hy
  have hCP : centralizer (P : Set G) ≤ D.M :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hyP)).trans (hC (y : G) hyP hyord)
  have hNP : normalizer (P : Set G) ≤ D.M := normalizer_le_of_controlsFusionIn hfus hCP
  have : IsSimpleGroup G := D.standing.simple
  have hMtop : D.M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top D.standing.nonab D.M D.maxLocal.1
  exact hcex.notStrong
    (CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le (s := 3)
      hMtop hcex.sylowP hPne hNP hC)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
