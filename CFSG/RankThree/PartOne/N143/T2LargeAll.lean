module

public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowLargePrime

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

@[expose] def Item4_1LargeAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
    ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal], layer (H ⧸ N) = ⊤ →
      ∀ p : ℕ, p.Prime → 3 < p → localRank p (H ⧸ N) < 3

namespace Item41Narrow

section Griess

theorem item4_1LargeAll_of_griess (hGA : GriessMultipliersAllModels) :
    Item4_1LargeAll := by
  intro G _ _ hG H N _ hS p hp hp3
  by_contra hlt
  have hfail : 2 < localRank p (H ⧸ N) := by omega
  have hK : CFSG.SectionRank.IsKGroupCat G :=
    PartOne.TCB.tcKGroupBridge G fun A B _ _ hs _ => hG.kGroup A (B.subgroupOf A) hs
  have he : CFSG.twoLocalOddRank G ≤ 3 := Census.SectionFourHyp.twoLocalOddRank_le hG
  have hr : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2 := fun r hr hr3 => by
    have := hG.localRank_lt r hr hr3
    omega
  classical
  have hex : ∃ n, ∃ U : Subgroup H, U.map (QuotientGroup.mk' N) = ⊤ ∧ Nat.card U = n :=
    ⟨_, ⊤, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), rfl⟩
  obtain ⟨X, hXS, hXn⟩ := Nat.find_spec hex
  have hXmin : ∀ U : Subgroup H, U.map (QuotientGroup.mk' N) = ⊤ → Nat.card X ≤ Nat.card U :=
    fun U hU => by
      rw [hXn]
      exact Nat.find_min' hex ⟨U, hU, rfl⟩
  obtain ⟨_, _, _, f, -, -, -, hA, -, -, -, hEY, -, hcomp⟩ :=
    OddKernel.original_central_failure_components hK he hr H N hS hp hp3 (Or.inl hfail) X hXS
      hXmin
  obtain ⟨_, _, _, -, -, -, -, -, -, -, -, halt, -⟩ :=
    OddKernel.original_central_failure_excludes_Ree_Suzuki_and_twelve_sporadic_components hK he
      hr H N hS hp hp3 (Or.inl hfail) X hXS hXmin
  obtain ⟨K, hKc⟩ := exists_isComponent hEY hA
  obtain ⟨hZ, hZp, -⟩ := hcomp K hKc
  have hpZ : p ∣ Nat.card (Subgroup.center K) := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd (Subgroup.card_eq_one.mp hk) hZ
    · rw [hk]
      exact dvd_pow_self p k.succ_ne_zero
  have heX : CFSG.Assembly.evenRank X ≤ 3 :=
    (evenRank_subgroup_le X).trans ((evenRank_subgroup_le H).trans hG.evenRank_le)
  rcases (halt K hKc).1 with ⟨τ, hτ, ℓ, d, -, -, hM, -⟩ |
      (⟨s, -, ⟨e⟩, -⟩ | ⟨s, -, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩) | hMs
  · exact PartOne.Mult.exceptionalCenterSmallPrimes_of_griess hGA K hKc.1
      (Or.inl ⟨τ, ℓ, d, hτ, hM⟩) p hp hp3 hpZ
  · have := four_le_evenRank_of_sporadic (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      hKc.1 hp hp3 hpZ e
    omega
  · have := four_le_evenRank_of_sporadic (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      hKc.1 hp hp3 hpZ e
    omega
  · have := four_le_evenRank_of_sporadic (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      hKc.1 hp hp3 hpZ e
    omega
  · obtain ⟨e⟩ := hMs
    have := four_le_evenRank_of_sporadic (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      hKc.1 hp hp3 hpZ e
    omega

end Griess

end Item41Narrow

end CFSG.RankThree.PartTwo.Sec4
