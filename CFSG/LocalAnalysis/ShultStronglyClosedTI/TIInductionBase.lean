module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OrderTwoEmbedding
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalInductionDatum
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

@[expose] def BoundedInvolutionPointCriterion (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y ≤ n →
    ∀ (H : Subgroup Y) (z : Y), InvolutionPointLocalEmbedding H z →
      (∃ S : Sylow 2 Y, ∃ hzS : z ∈ (S : Subgroup Y),
        (⟨z, hzS⟩ : (S : Subgroup Y)) ∈ Subgroup.center (S : Subgroup Y)) →
      fusionStronglyEmbedded (H.subgroupOf (involutionPointHull z))

theorem ti_induction_card_ge_four (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hcard : Nat.card U ≠ 2) :
    4 ≤ Nat.card U := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 U :=
    T.isPGroup'.of_injective (Subgroup.inclusion hUT) (Subgroup.inclusion_injective hUT)
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra h
    have hsmall : k = 0 ∨ k = 1 := by omega
    rcases hsmall with hzero | hone
    · exact hU (Subgroup.card_eq_one.mp (by simpa only [hzero, pow_zero] using hk))
    · exact hcard (by simpa only [hone, pow_one] using hk)
  have h := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) hk2
  rw [← hk] at h
  norm_num at h ⊢
  exact h

theorem ti_induction_order_two_embedding (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hcard : Nat.card U = 2)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hnormal : ¬ U.Normal) :
    fusionStronglyEmbedded ((Subgroup.normalizer (U : Set G)).subgroupOf
      (Subgroup.normalClosure (U : Set G))) := by
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hz : orderOf (z : G) = 2 := by
    have hd : orderOf (z : G) ∣ 2 := hcard ▸ Subgroup.orderOf_dvd_natCard U z.property
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (hzne (Subtype.ext (orderOf_eq_one_iff.mp h))).elim
    · exact h
  have hUeq : Subgroup.zpowers (z : G) = U :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z.property)
      (by rw [Nat.card_zpowers, hz, hcard])
  have h := (order_two_hull_strong_embedding T (z : G) (hUT z.property) hz
    (hUeq.symm ▸ hclosed) (hUeq.symm ▸ hnormal)).2.2.2.2.2
  rw [← normalizer_zpowers_eq_centralizer hz,
    involutionPointHull_eq_normalClosure_zpowers, hUeq] at h
  exact h

theorem ti_induction_no_central_involution_embedding (n : ℕ)
    (hLC : BoundedInvolutionPointCriterion n) (hbound : Nat.card G ≤ n)
    (T : Sylow 2 G) (U : Subgroup G) (hUT : U ≤ (T : Subgroup G))
    (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (hno : ∀ c ∈ Subgroup.center G, orderOf c ≠ 2)
    (hsmaller : SmallerTIHullEmbeddings.{0} (Nat.card G)) :
    fusionStronglyEmbedded ((Subgroup.normalizer (U : Set G)).subgroupOf
      (Subgroup.normalClosure (U : Set G))) := by
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hzneG : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  obtain ⟨hdatum, hcentral, hhull⟩ := no_central_involution_local_induction_datum
    T U hUT hU hUel hclosed hTI hnormal hno hsmaller z z.property hzneG
  have h := hLC G hbound (Subgroup.normalizer (U : Set G)) z hdatum hcentral
  rw [hhull] at h
  exact h

omit [Finite G] in
theorem ti_simple_elementary_hull [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (U : Subgroup G)
    (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U) :
    ¬ U.Normal ∧ Subgroup.normalClosure (U : Set G) = ⊤ := by
  have hnormal : ¬ U.Normal := by
    intro h
    rcases h.eq_bot_or_eq_top with hbot | htop
    · exact hU hbot
    · obtain ⟨a, b, hab⟩ := hnonab
      let aU : U := ⟨a, htop.symm ▸ Subgroup.mem_top a⟩
      let bU : U := ⟨b, htop.symm ▸ Subgroup.mem_top b⟩
      exact hab (congrArg Subtype.val (hUel.1.is_comm.comm aU bU))
  refine ⟨hnormal, ?_⟩
  rcases (inferInstance : (Subgroup.normalClosure (U : Set G)).Normal).eq_bot_or_eq_top
      with hbot | htop
  · exact (hU (bot_unique (hbot ▸ (Subgroup.le_normalClosure (H := U))))).elim
  · exact htop

theorem ti_simple_rank_and_odd_core [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) :
    4 ≤ Nat.card U ∧ TwoRankAtLeastTwo G ∧ oddCore G = ⊥ := by
  have hcard : 4 ≤ Nat.card U := ti_induction_card_ge_four T U hUT hU
    (no_order_two_strongly_closed hnonab T U hUT hclosed)
  have hrank : TwoRankAtLeastTwo G :=
    (twoRankAtLeastTwo_of_elementary_card_ge_four U hUel hcard).map_of_injective
      U.subtype U.subtype_injective
  refine ⟨hcard, hrank, ?_⟩
  rcases (inferInstance : (oddCore G).Normal).eq_bot_or_eq_top with hbot | htop
  · exact hbot
  · obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
    have hz : orderOf (z : G) = 2 := orderOf_eq_prime_iff.mpr
      ⟨hUel.2 z z.property, fun h => hzne (Subtype.ext h)⟩
    exact (CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hz
      (htop.symm ▸ Subgroup.mem_top z)).elim

end CFSG.ShultStronglyClosedTI
