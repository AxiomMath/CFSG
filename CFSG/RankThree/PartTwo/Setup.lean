module

public import CFSG.RankThree.PartTwo.Notation
public import CFSG.Foundations.Catalog
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.LocalAnalysis.ComponentInitial.KProperLocal

public section

namespace CFSG.RankThree.PartTwo

open CFSG CFSG.RankThree.LocalRank
open CFSG.Assembly (KProper InCatalog IsCharTwoType evenRank IsTwoLocal)
open CFSG.Assembly.RankThreeEven (localRank sigmaA aschCore AschCoreLocal IIModel)

structure TheoremFourHyp (G : Type) [Group G] [Finite G] : Prop where
  isSimpleGroup : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kProper : KProper InCatalog G
  charTwoType : IsCharTwoType G
  evenRank_eq : evenRank G = 3
  localRank_lt : ∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3

structure PartTwoStanding (G : Type) [Group G] [Finite G] : Prop extends TheoremFourHyp G where
  not_inCatalog : ¬ InCatalog G

@[expose] def TheoremFourTwo (G : Type) [Group G] [Finite G] : Prop :=
  ∀ P : Sylow 3 G, ∃ H : Subgroup G, IsTwoLocal H ∧ gammaZero (P : Subgroup G) ≤ H

namespace TheoremFourHyp

variable {G : Type} [Group G] [Finite G]

theorem sigmaA_eq (h : TheoremFourHyp G) : sigmaA G = {3} :=
  (rank_three_selector_eq_three_iff h.evenRank_eq).mpr h.localRank_lt

theorem localRank_three (h : TheoremFourHyp G) : localRank 3 G = 3 :=
  rank_three_selector_localRank_eq h.evenRank_eq (h.sigmaA_eq ▸ Set.mem_singleton 3)

theorem partTwoF_diff_partTwoE_subset (h : TheoremFourHyp G) :
    partTwoF G \ partTwoE G ⊆ partTwoS G :=
  (part_two_empty_odd_collection_rank_three_reduction h.localRank_three.le).1

theorem partTwoF_eq_partTwoE (h : TheoremFourHyp G) (hS : partTwoS G = ∅) :
    partTwoF G = partTwoE G ∧ (partTwoE G).Nonempty := by
  obtain ⟨-, -, heq, hne⟩ :=
    part_two_empty_odd_collection_rank_three_reduction (G := G) h.localRank_three.le
  exact ⟨heq hS, (hne hS h.localRank_three).2⟩

theorem aschCoreLocal_two_iff (h : TheoremFourHyp G) : AschCoreLocal G 2 ↔ TheoremFourTwo G := by
  simp only [AschCoreLocal, TheoremFourTwo, h.sigmaA_eq, Set.mem_singleton_iff, forall_eq]

end TheoremFourHyp

structure SectionFourHyp (G : Type) [Group G] [Finite G] : Prop where
  kGroup : IsKGroup G
  evenRank_le : evenRank G ≤ 3
  localRank_lt : ∀ p : ℕ, p.Prime → 3 < p → localRank p G < 3

theorem exists_isTwoLocal_map_subtype_le {G : Type*} [Group G] {H : Subgroup G}
    {X : Subgroup H} (hX : IsTwoLocal X) :
    ∃ Y : Subgroup G, IsTwoLocal Y ∧ X.map H.subtype ≤ Y := by
  obtain ⟨P, hP, hP2, rfl⟩ := hX
  exact ⟨_, ⟨P.map H.subtype,
    fun h => hP ((Subgroup.map_eq_bot_iff_of_injective P H.subtype_injective).mp h),
    hP2.map _, rfl⟩, Subgroup.le_normalizer_map _⟩

theorem localRank_subgroup_le {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) : localRank p H ≤ localRank p G := by
  apply csSup_le'
  rintro _ ⟨X, hX, rfl⟩
  obtain ⟨Y, hY, hXY⟩ := exists_isTwoLocal_map_subtype_le hX
  have hle : CFSG.Open.pRank p X ≤ CFSG.Open.pRank p Y :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p hp H.subtype
      H.subtype_injective X).trans (CFSG.RankThreeEvenClassification.Helpers.pRank_mono p hp hXY)
  refine hle.trans (le_csSup ⟨Nat.card G, ?_⟩ ⟨Y, hY, rfl⟩)
  rintro _ ⟨Z, -, rfl⟩
  exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp Z).trans
    (Subgroup.card_le_card_group Z)

theorem evenRank_subgroup_le {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    evenRank H ≤ evenRank G := by
  apply csSup_le'
  rintro _ ⟨p, X, hp, hp2, hX, rfl⟩
  obtain ⟨Y, hY, hXY⟩ := exists_isTwoLocal_map_subtype_le hX
  exact ((CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p hp H.subtype
    H.subtype_injective X).trans (CFSG.RankThreeEvenClassification.Helpers.pRank_mono p hp
      hXY)).trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 Y hY)

theorem TheoremFourHyp.sectionFourHyp {G : Type} [Group G] [Finite G] (h : TheoremFourHyp G)
    {H : Subgroup G} (hH : H ≠ ⊤) : SectionFourHyp H :=
  ⟨(CFSG.LocalAnalysis.ComponentInitial.k_proper_local
      (CFSG.LocalAnalysis.ComponentInitial.isKProper_of_kProper h.kProper)).1 H
      (lt_top_iff_ne_top.mpr hH),
    (evenRank_subgroup_le H).trans h.evenRank_eq.le,
    fun p hp h3 => (localRank_subgroup_le hp H).trans_lt (h.localRank_lt p hp h3)⟩

theorem theoremFourTwo_iff {G : Type} [Group G] [Finite G] :
    TheoremFourTwo G ↔
      ∀ P : Sylow 3 G, (scriptM (gammaZero (P : Subgroup G) : Set G)).Nonempty := by
  refine forall_congr' fun P => ?_
  rw [scriptM_nonempty_iff]
  exact exists_congr fun H => and_congr_right fun _ => SetLike.coe_subset_coe.symm

@[expose] def Item433 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], TheoremFourHyp G → InCatalog G → IIModel G

@[expose] def Item236 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → partTwoS G = ∅

@[expose] def Item2011 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → partTwoS G = ∅ →
    ∀ P : Sylow 3 G, (scriptM (gammaZero (P : Subgroup G) : Set G)).Nonempty

theorem TheoremFourHyp.conclusion (h433 : Item433) (h236 : Item236) (h2011 : Item2011)
    {G : Type} [Group G] [Finite G] (h : TheoremFourHyp G) : IIModel G ∨ AschCoreLocal G 2 := by
  by_cases hcat : InCatalog G
  · exact Or.inl (h433 G h hcat)
  · have hst : PartTwoStanding G := { h with not_inCatalog := hcat }
    exact Or.inr (h.aschCoreLocal_two_iff.mpr (theoremFourTwo_iff.mpr (h2011 G hst (h236 G hst))))

theorem theorem_four_of_items (h433 : Item433) (h236 : Item236) (h2011 : Item2011) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      KProper InCatalog G → IsCharTwoType G → evenRank G = 3 →
      (∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3) → IIModel G ∨ AschCoreLocal G 2 :=
  fun _ _ _ _ hnonab hK hchar he hq =>
    TheoremFourHyp.conclusion h433 h236 h2011 ⟨inferInstance, hnonab, hK, hchar, he, hq⟩

end CFSG.RankThree.PartTwo
