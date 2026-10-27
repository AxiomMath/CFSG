module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res3ProofTypes
public import CFSG.RankThree.PartTwo.Sec21.Item21Res6ProofNoField

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item2130Res4Proof

variable {G : Type} [Group G] [Finite G]

theorem exists_invTwoBarNontrivial {A Y : Subgroup G} (hY : Y ∈ lZeroUnion A) :
    ∃ E' ∈ partTwoE G, E' ≤ A ∧ Sec8.InvTwoBarNontrivial E' Y := by
  obtain ⟨E', hE', hE'A, -, U', hU', hcomm⟩ := mem_lZeroUnion_iff.mp hY
  refine ⟨E', hE', hE'A, ?_⟩
  obtain ⟨hU'Y, hU'2, hE'U'⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hU'
  set θY := aschbacherSolvableCore 3 Y with hθY
  refine ⟨(U'.subgroupOf Y).map (QuotientGroup.mk' θY), ?_, ?_, ?_⟩
  · intro hbot
    apply hcomm
    have hU'θ : U' ≤ inSubgroup (aschbacherSolvableCore 3) Y := by
      intro u hu
      have hmem : QuotientGroup.mk' θY (⟨u, hU'Y hu⟩ : Y) ∈
          (U'.subgroupOf Y).map (QuotientGroup.mk' θY) := ⟨⟨u, hU'Y hu⟩, hu, rfl⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact ⟨_, hmem, rfl⟩
    rw [Subgroup.commutator_le]
    intro u hu e he
    have h1 : e * u⁻¹ * e⁻¹ ∈ U' :=
      (Subgroup.mem_normalizer_iff.mp (hE'U' he) u⁻¹).mp (U'.inv_mem hu)
    rw [commutatorElement_def]
    have : u * e * u⁻¹ * e⁻¹ = u * (e * u⁻¹ * e⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ (hU'θ hu) (hU'θ h1)
  · exact (hU'2.comap_of_injective Y.subtype Y.subtype_injective).map _
  · intro τ hτ y hy
    obtain ⟨h, hN, hE, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    obtain ⟨⟨q, hqY⟩, hq, rfl⟩ := hy
    have hqU : q ∈ U' := Subgroup.mem_subgroupOf.mp hq
    have hhq : h * q * h⁻¹ ∈ U' := (Subgroup.mem_normalizer_iff.mp (hE'U' hE) q).mp hqU
    exact ⟨⟨h * q * h⁻¹, hU'Y hhq⟩, Subgroup.mem_subgroupOf.mpr hhq, rfl⟩

end Item2130Res4Proof

open Item2130Res4Proof

section Certs

theorem item2130NoFieldY_of (h1134 : Sec11.Item1134E27) (hST : Item1134E27ST) :
    Item2130NoFieldY := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC x hx
  have hpair := hcfg.pair
  have h27 : Nat.card A = 3 ^ 3 := by rw [hcfg.card_eq, h9]; norm_num
  have h27' : Nat.card A = 27 := by rw [h27]; norm_num
  have hEF : partTwoE G = partTwoF G := hpair.side (mem_partTwoE_of_card hpair h27)
  have hYs : Y ∈ lStarAt A b :=
    ⟨lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A b hC.y_mem),
      lZeroStarAt_subset A b hC.y_mem⟩
  have hY0 : Y ∈ lZeroUnion A :=
    lZeroStar_subset_lZeroUnion A (lZeroStarAt_subset_lZeroStar A b hC.y_mem)
  have hbA : b ∈ A := hC.b_mem.1
  by_cases hAT : A ∈ partTwoT G
  · exact hST G A b Y hpair.standing hpair.mem_S hAT h27' hbA hC.b_ne_one hYs hC.sec_cent
      (Or.inl (exists_invTwoBarNontrivial hY0)) hEF x hx
  · exact h1134 G A b Y hpair.standing hpair.mem_S.1 hAT h27' hbA hC.b_ne_one hYs hC.sec_cent
      (Or.inl (exists_invTwoBarNontrivial hY0)) (fun _ => hEF) x hx

end Certs

end CFSG.RankThree.PartTwo.Sec21
