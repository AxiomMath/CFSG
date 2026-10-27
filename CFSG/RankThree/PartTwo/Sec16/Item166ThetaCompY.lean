module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple
public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.PerfectCentralExtensionUnique

public section

namespace CFSG.RankThree.PartTwo.Sec16.ThetaCompY

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.GH74.GLS

theorem eq_bot_of_normal_of_not_three_dvd {T : Type*} [Group T] [Finite T]
    [Group.IsPerfect T] (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    {N : Subgroup T} [N.Normal] (hN : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  classical
  let σ : T →* alternatingGroup (Fin 6) :=
    hT.2.some.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center T))
  have hσ : Function.Surjective σ :=
    hT.2.some.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center T))
  have hker : σ.ker = Subgroup.center T := by
    change (hT.2.some.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center T))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ hT.2.some.injective, QuotientGroup.ker_mk']
  haveI hNn : (N.map σ).Normal := Subgroup.Normal.map inferInstance σ hσ
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 6) (by simp)
    (N := N.map σ) with hbot | htop
  · have hle : N ≤ Subgroup.center T := by
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff (f := σ) N).mp hbot
    have hdvd : Nat.card N ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [hT.1] at h
    have h1 : Nat.card N = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exact h1
      · rw [h1] at hN
        exact absurd dvd_rfl hN
    exact (Subgroup.card_eq_one (H := N)).mp h1
  · have hsup : N ⊔ σ.ker = ⊤ := by
      have h := htop
      rw [← MonoidHom.range_eq_top.mpr hσ] at h
      exact codisjoint_iff.mp (Subgroup.map_eq_range_iff.mp h)
    have hNtop : N = ⊤ :=
      CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect (L := N) (Z := σ.ker)
        (by rw [hker]) hsup
    have h3N : 3 ∣ Nat.card N := by
      rw [hNtop, Subgroup.card_top]
      have h := Subgroup.card_subgroup_dvd_card (Subgroup.center T)
      rwa [hT.1] at h
    exact absurd h3N hN

theorem inf_pPrimeCoreOf_eq {G : Type*} [Group G] [Finite G] {H X : Subgroup G}
    (hX : X ∈ thetaComponentsIn H)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
      (alternatingGroup (Fin 6))) :
    X ⊓ pPrimeCoreOf 3 H = (aschbacherSolvableCore 3 ↥X).map X.subtype := by
  obtain ⟨L, hL, hXdef⟩ := hX
  have hXH : X ≤ H := by
    rw [← hXdef]
    exact Subgroup.map_subtype_le L
  have hcomp : ((L.map H.subtype).subtype).comp
      (L.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom =
      H.subtype.comp L.subtype := by
    ext x
    rfl
  have hθ : (aschbacherSolvableCore 3 ↥X).map X.subtype =
      ((aschbacherSolvableCore 3 L).map L.subtype).map H.subtype := by
    rw [← hXdef, ← CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three
      (L.equivMapOfInjective H.subtype H.subtype_injective)]
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  apply le_antisymm
  ·
    let U : Subgroup G := X ⊓ pPrimeCoreOf 3 H
    have hUX : U ≤ X := inf_le_left
    have hHP : H ≤ Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) := by
      have h1 := Subgroup.le_normalizer_map (H := CFSG.pPrimeCore 3 ↥H) H.subtype
      rw [Subgroup.normalizer_eq_top (H := CFSG.pPrimeCore 3 ↥H),
        ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
      exact h1
    have hXN : X ≤ Subgroup.normalizer (U : Set G) := by
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr
        ⟨Subgroup.le_normalizer hx, (hXH.trans hHP) hx⟩)
    haveI hUn : (U.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hUX).mpr hXN
    have hP3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 H) := by
      unfold pPrimeCoreOf
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
    have hU3 : ¬ 3 ∣ Nat.card U := fun h =>
      hP3 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
    have hcard : Nat.card (U.subgroupOf X) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv
    have hU3sub : ¬ 3 ∣ Nat.card (U.subgroupOf X) := by
      rwa [hcard]
    haveI hperfX : Group.IsPerfect ↥X := by
      rw [← hXdef]
      exact isPerfect_map_subtype hL.1
    let π : ↥X →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)
    haveI hNmap : ((U.subgroupOf X).map π).Normal :=
      hUn.map π (QuotientGroup.mk'_surjective _)
    have h3map : ¬ 3 ∣ Nat.card ((U.subgroupOf X).map π) := fun h =>
      hU3sub (h.trans (Subgroup.card_map_dvd _ π))
    have hbot : (U.subgroupOf X).map π = ⊥ :=
      eq_bot_of_normal_of_not_three_dvd (T := ↥X ⧸ aschbacherSolvableCore 3 ↥X)
        (N := (U.subgroupOf X).map π) hT h3map
    have hUθ : U.subgroupOf X ≤ aschbacherSolvableCore 3 ↥X := by
      rw [← QuotientGroup.ker_mk' (aschbacherSolvableCore 3 ↥X)]
      exact (Subgroup.map_eq_bot_iff (f := π) (U.subgroupOf X)).mp hbot
    calc U = (U.subgroupOf X).map X.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hUX).symm
      _ ≤ (aschbacherSolvableCore 3 ↥X).map X.subtype := Subgroup.map_mono hUθ
  ·
    have hθLle : inSubgroup (aschbacherSolvableCore 3) L ≤ CFSG.pPrimeCore 3 ↥H := by
      rw [solvable_prime_complement_core_subnormal_intersection Nat.prime_three hL.2.1]
      exact inf_le_right.trans
        (CFSG.GroupTheory.le_pPrimeCore_of_normal inferInstance
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
            (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1))
    rw [hθ]
    refine le_inf ?_ ?_
    · rw [← hXdef]
      exact Subgroup.map_mono (Subgroup.map_subtype_le (aschbacherSolvableCore 3 L))
    · exact Subgroup.map_mono hθLle

end CFSG.RankThree.PartTwo.Sec16.ThetaCompY