module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabelDefs
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Blueprint.Multiplier (generic exceptional genericOrders exceptionalOrders)
open CFSG.RankThree.PerfectCover (hopfMultiplier hopfMultiplierEquivGriess hopfMultiplierToKer
  hopfMultiplierToKer_surjective centralQuotientMap centralQuotientMap_ker
  centralQuotientMap_surjective)

private theorem l05nL4s_card_center_dvd_hopfMultiplier {K S : Type} [Group K] [Group S]
    [Group.IsPerfect K] (e : K ⧸ Subgroup.center K ≃* S) :
    Nat.card (Subgroup.center K) ∣ Nat.card (hopfMultiplier S) := by
  have hker := centralQuotientMap_ker e
  have h := Subgroup.card_dvd_of_surjective
    (hopfMultiplierToKer_surjective (centralQuotientMap e)
      (centralQuotientMap_surjective e) hker.le)
  rwa [hker] at h

private theorem l05nL4s_orders_dvd_twelve (lab : LargeEvenLabel)
    (h : GGE6DepLabel lab ∨ GGA5Label lab) :
    (genericOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).1 *
        (genericOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).2 *
        ((exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).1 *
          (exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).2) ∣
      12 := by
  obtain ⟨t, l, n⟩ := lab
  rcases h with hE6 | hA5
  · rcases hE6 with ⟨ht, hd⟩ | ⟨ht, hd⟩
    ·
      subst ht
      simp only [markTag, markRank, markChar, markDeg, genericOrders, exceptionalOrders]
      rw [Nat.gcd_eq_left hd]
      norm_num
    ·
      subst ht
      by_cases hn1 : n = 1
      · subst hn1
        simp only [markTag, markRank, markChar, markDeg, genericOrders, exceptionalOrders]
        norm_num
      · have he : exceptionalOrders .twistedE6 0 2 n = (1, 1) := by
          unfold exceptionalOrders
          split <;> first | rfl | (exfalso; simp_all)
        simp only [markTag, markRank, markChar, markDeg, genericOrders, he]
        have h3 : Nat.gcd 3 (2 ^ n + 1) ∣ 3 := Nat.gcd_dvd_left _ _
        simpa using h3.trans (by norm_num : 3 ∣ 12)
  · rcases hA5 with ⟨hr, hd⟩
    rcases hd with ⟨ht, hd⟩ | ⟨ht, hd⟩
    ·
      subst ht
      subst hr
      simp only [markTag, markRank, markChar, markDeg, genericOrders, exceptionalOrders]
      have h6 : Nat.gcd 6 (2 ^ n - 1) ∣ 6 := Nat.gcd_dvd_left _ _
      simpa using h6.trans (by norm_num : 6 ∣ 12)
    ·
      subst ht
      subst hr
      by_cases hn1 : n = 1
      · subst hn1
        simp only [markTag, markRank, markChar, markDeg, genericOrders, exceptionalOrders]
        norm_num
      · have he : exceptionalOrders .PSU 6 2 n = (1, 1) := by
          unfold exceptionalOrders
          split <;> first | rfl | (exfalso; simp_all)
        simp only [markTag, markRank, markChar, markDeg, genericOrders, he]
        have h6 : Nat.gcd 6 (2 ^ n + 1) ∣ 6 := Nat.gcd_dvd_left _ _
        simpa using h6.trans (by norm_num : 6 ∣ 12)

theorem ggSchurDvdInput_holds :
    GGSchurDvdInput := by
  intro X _ _ lab hperf hL2 hlab hl
  by_cases hn : Nontrivial (X ⧸ Subgroup.center X)
  · obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hperf hn
    obtain ⟨R, _, I, F, ⟨e⟩, hm⟩ := largeEvenRawDatum_exists
      (largeEvenRawDatum_markedModel hL2
        (Q := fun R' _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R'))
        (by
          rintro R _ I F ⟨e⟩
          exact nonabelian_of_mulEquiv e ⟨a, b, hab⟩)
        hl)
    have hM : MarkedModel lab (X ⧸ Subgroup.center X) := MarkedModel.of_mulEquiv e.symm hm
    have : Group.IsPerfect X := ⟨hperf⟩
    have hdiv : Nat.card (Subgroup.center X) ∣
        Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) :=
      l05nL4s_card_center_dvd_hopfMultiplier
        (K := X) (S := X ⧸ Subgroup.center X) (MulEquiv.refl _)
    obtain ⟨-, hT⟩ :=
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ _ _ _ _ hM
    have hcard : Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) =
        (genericOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).1 *
          (genericOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).2 *
          ((exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).1 *
            (exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).2) := by
      obtain ⟨eg⟩ := hT
      let e' : hopfMultiplier (X ⧸ Subgroup.center X) ≃*
          generic (markTag lab) (markRank lab) (markChar lab) (markDeg lab) ×
            exceptional (markTag lab) (markRank lab) (markChar lab) (markDeg lab) :=
        (hopfMultiplierEquivGriess (X ⧸ Subgroup.center X)).symm.trans eg
      rw [Nat.card_congr e'.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod]
      simp [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [hcard] at hdiv
    exact hdiv.trans (l05nL4s_orders_dvd_twelve lab hlab)
  · have hZ : Subgroup.center X = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro g
      have : Subsingleton (X ⧸ Subgroup.center X) := not_nontrivial_iff_subsingleton.mp hn
      exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
    have : Group.IsPerfect X := ⟨hperf⟩
    have : IsMulCommutative X := Subgroup.center_eq_top_iff.mp hZ
    have : Subsingleton X := inferInstance
    have h1 : Nat.card (Subgroup.center X) = 1 := by
      have hle : Nat.card (Subgroup.center X) ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.mpr inferInstance
      have hpos : 1 ≤ Nat.card (Subgroup.center X) := by
        haveI : Nonempty (Subgroup.center X) := ⟨⟨1, Subgroup.one_mem _⟩⟩
        exact Nat.card_pos
      omega
    rw [h1]
    exact one_dvd 12

end CFSG.StandardType
