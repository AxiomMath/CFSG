module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Inputs
public import CFSG.RankThree.PartTwo.Sec21.FF84S4KF43Act
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalM12
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartOne.S10.CyclicSemisimpleSectionOrbit
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.Assembly (InCatalog)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

section Radical

variable {H : Type} [Group H] [Finite H]

theorem kf43_image_normal :
    ((pPrimeCore 3 H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))).Normal :=
  Subgroup.Normal.map pPrimeCore_normal _ (QuotientGroup.mk'_surjective _)

theorem kf43_image_not_dvd_three :
    ¬ 3 ∣ Nat.card ((pPrimeCore 3 H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 : ¬ 3 ∣ Nat.card (pPrimeCore 3 H) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 pPrimeCore_coprime_card
  have hd : Nat.card ((pPrimeCore 3 H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) ∣
      Nat.card (pPrimeCore 3 H) :=
    Subgroup.card_dvd_of_surjective
      (f := (QuotientGroup.mk' (aschbacherSolvableCore 3 H)).subgroupMap (pPrimeCore 3 H))
      (MonoidHom.subgroupMap_surjective _ _)
  exact fun h => hN3 (h.trans hd)

theorem kf43_radical_free_image :
    solvableRadical ↥((pPrimeCore 3 H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) =
      ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hΘs, -, hΘ3, hΘmax, -⟩ :=
    RankThree.LocalRank.solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  have hQ3 := kf43_image_not_dvd_three (H := H)
  set Θ := aschbacherSolvableCore 3 H with hΘ
  set π : H →* H ⧸ Θ := QuotientGroup.mk' Θ with hπ
  set Qs : Subgroup (H ⧸ Θ) := (pPrimeCore 3 H).map π with hQs
  haveI hQn : Qs.Normal := kf43_image_normal
  refine eq_bot_iff.2 fun r hr => ?_
  set R := solvableRadical ↥Qs with hR
  haveI hRs : Group.IsSolvable R :=
    SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  haveI hRc : R.Characteristic :=
    SignalizerFunctorTheorem.Nonsolvable.solvableRadical_characteristic
  haveI hRn : (R.map Qs.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  set Rt : Subgroup (H ⧸ Θ) := R.map Qs.subtype with hRt
  haveI hRts : Group.IsSolvable Rt :=
    solvable_of_surjective (MonoidHom.subgroupMap_surjective Qs.subtype R)
  set R' : Subgroup H := Rt.comap π with hR'
  haveI hR'n : R'.Normal := hRn.comap π
  have hΘR' : Θ ≤ R' := fun x hx => by
    show π x ∈ Rt
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  haveI hR's : Group.IsSolvable R' := by
    refine solvable_of_ker_le_range (Subgroup.inclusion hΘR') (π.subgroupComap Rt) ?_
    intro x hx
    have h1 : π (x : H) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      exact this
    have h2 : (x : H) ∈ Θ := (QuotientGroup.eq_one_iff _).1 h1
    exact ⟨⟨x, h2⟩, Subtype.ext rfl⟩
  have hRtQ : ∀ y ∈ Rt, y ∈ Qs := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have h3R' : ¬ 3 ∣ Nat.card R' := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R') 3 hd
    have hx3 : (x : H) ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this
    have hxo : orderOf (x : H) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    by_cases h1 : π (x : H) = 1
    · have hxΘ : (x : H) ∈ Θ := (QuotientGroup.eq_one_iff _).1 h1
      have := Subgroup.orderOf_dvd_natCard Θ hxΘ
      rw [hxo] at this
      exact hΘ3 this
    · have hpx3 : (π (x : H)) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
      have hpo : orderOf (π (x : H)) = 3 := orderOf_eq_prime hpx3 h1
      have hxQ : π (x : H) ∈ Qs := hRtQ _ x.2
      have := Subgroup.orderOf_dvd_natCard Qs hxQ
      rw [hpo] at this
      exact hQ3 this
  have hR'le : R' ≤ Θ := hΘmax R' hR'n hR's h3R'
  obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective Θ (r : H ⧸ Θ)
  have hrRt : (r : H ⧸ Θ) ∈ Rt := ⟨r, hr, rfl⟩
  have hhR' : h ∈ R' := by
    show π h ∈ Rt
    rw [show π h = (r : H ⧸ Θ) from hh]
    exact hrRt
  have : π h = 1 := (QuotientGroup.eq_one_iff h).2 (hR'le hhR')
  rw [Subgroup.mem_bot]
  exact Subtype.ext (hh.symm.trans this)

end Radical

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
