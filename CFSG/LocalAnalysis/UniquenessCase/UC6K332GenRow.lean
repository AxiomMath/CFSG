module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Gen
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Main

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts (centerDescend)

theorem k432InnerThreeP_of_goodRow (PL : ∀ (L : Type) [Group L] [Finite L], Prop)
    (hrow : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → PL L →
      GoodRow (L ⧸ Subgroup.center L)) : K432InnerThreeP PL := by
  intro L _ _ hq hS h3 σ hσ3 hσ1 hwc
  haveI : Group.IsPerfect L := hq.1
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  have hZS := center_eq_bot_of_isQuasisimple_quot hq
  obtain ⟨hlist, houter⟩ := hrow L hq hS
  have hinj : Function.Injective (centerDescend L) := Res423Five.centerDescend_injective
  have hρσ3 : centerDescend L σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  have hρσ1 : centerDescend L σ ≠ 1 := fun h => hσ1 (hinj (by rw [h, map_one]))
  have hwc' : AutWeaklyClosed (centerDescend L σ) := autWeaklyClosed_descend hwc
  by_cases hin : centerDescend L σ ∈
      (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range
  · obtain ⟨bb, hbb⟩ := hin
    have hcinj := conj_injective_of_center_eq_bot hZS
    have hbb3 : bb ^ 3 = 1 := by
      apply hcinj
      rw [map_pow, hbb, hρσ3, map_one]
    have hbb1 : bb ≠ 1 := by
      intro h
      apply hρσ1
      rw [← hbb, h, map_one]
    have horder : orderOf bb = 3 := orderOf_eq_prime hbb3 hbb1
    have hwcb : WeaklyClosed (Subgroup.zpowers bb) :=
      weaklyClosed_zpowers_of_autWeaklyClosed_conj hZS (by rw [hbb]; exact hwc')
    have hreal : ∃ t : L ⧸ Subgroup.center L, t * bb * t⁻¹ = bb⁻¹ := by
      rcases hlist bb horder hwcb with h1 | ⟨-, hr, -⟩ | ⟨-, hr, -⟩
      · exact exists_inv_of_pRank_one hq.2.2 h1 horder
      · exact hr bb hbb3
      · exact hr bb hbb3
    obtain ⟨tt, htt⟩ := hreal
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective bb
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective tt
    refine ⟨b, t, hinj (hbb.symm.trans (Res423Five.centerDescend_conj' b).symm), ?_⟩
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [htt]
    group
  · exact absurd hwc' (houter (three_dvd_card_quot_center hq.1 h3) _ hρσ3 hin)

theorem k432ListP_of_goodRow (PL : ∀ (L : Type) [Group L] [Finite L], Prop)
    (hrow : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → PL L →
      GoodRow (L ⧸ Subgroup.center L)) : K432ListP PL := by
  intro L _ _ hq hS hZ3 Z hZ hwc hnc
  haveI : Group.IsPerfect L := hq.1
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  obtain ⟨z, hzo, rfl⟩ := Item432Proof.exists_zpowers_eq hZ
  have hzc : z ∉ Subgroup.center L := fun h => hnc (Subgroup.zpowers_le.mpr h)
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hbar : WeaklyClosed (Subgroup.zpowers (QuotientGroup.mk z : L ⧸ Subgroup.center L)) :=
    weaklyClosed_mk_zpowers hzo hzc hwc
  have hzbar3 : (QuotientGroup.mk z : L ⧸ Subgroup.center L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hz3, QuotientGroup.mk_one]
  have hzbar1 : (QuotientGroup.mk z : L ⧸ Subgroup.center L) ≠ 1 := fun h1 =>
    hzc ((QuotientGroup.eq_one_iff z).mp h1)
  obtain ⟨hlist, -⟩ := hrow L hq hS
  rcases hlist _ (orderOf_eq_prime hzbar3 hzbar1) hbar with h1 | ⟨hG2, -, hno⟩ | ⟨hJ2, -, hno⟩
  · have hbot : Subgroup.center L = ⊥ :=
      center_eq_bot_of_pRank_quot_le_one hq.1 hZ3 h1.le
    left
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
      (mulEquivQuotCenterOfEqBot hbot)]
    exact h1
  · have hbot : Subgroup.center L = ⊥ := hno L hq hZ3 ⟨MulEquiv.refl _⟩
    right; left
    obtain ⟨e⟩ : Nonempty (L ≃* (L ⧸ Subgroup.center L)) := ⟨mulEquivQuotCenterOfEqBot hbot⟩
    rcases hG2 with ⟨p, f, hm⟩ | he'
    · exact Or.inl ⟨p, f, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hm⟩
    · obtain ⟨e'⟩ := he'
      exact Or.inr ⟨e.trans e'⟩
  · have hbot : Subgroup.center L = ⊥ := hno L hq hZ3 ⟨MulEquiv.refl _⟩
    right; right
    obtain ⟨e'⟩ := hJ2
    exact ⟨(mulEquivQuotCenterOfEqBot hbot).trans e'⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
