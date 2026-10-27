module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec15.Wales154Stage
import CFSG.RankThree.PartTwo.Sec17.PropULemmaThree
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem type_facts {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Nonempty (X ≃* alternatingGroup (Fin 5))) :
    (∀ N : Subgroup X, N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥) ∧
      3 ∣ Nat.card (perfectResidual X) := by
  have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hA5card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  haveI hA6simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hA5simple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hresTop : ∀ {Y : Type} [Group Y] [Finite Y], Group.IsPerfect Y → perfectResidual Y = ⊤ := by
    intro Y _ _ hY
    haveI := hY
    exact eq_top_iff.2 ((CFSG.perfect_residual_transport (MonoidHom.id Y)).2.2 ⊤ inferInstance)
  have key : ∀ {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y],
      ¬ (Nat.card Y).Prime → 3 ∣ Nat.card Y →
      (∀ N : Subgroup Y, N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥) ∧
        3 ∣ Nat.card (perfectResidual Y) := by
    intro Y _ _ hsimple hprime h3
    have hperf : Group.IsPerfect Y := (isPerfect_center_of_isSimpleGroup hsimple hprime).1
    refine ⟨?_, ?_⟩
    · intro N hN h3N
      rcases hsimple.eq_bot_or_eq_top_of_normal N with h | h
      · exact h
      · exfalso
        exact h3N (by rw [h, Subgroup.card_top]; exact h3)
    · rw [hresTop hperf, Subgroup.card_top]
      exact h3
  rcases hX with he | htc | he
  ·
    obtain ⟨e⟩ := he
    haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 :=
      CFSG.Sporadic.J2.isSimpleGroup_J2
    haveI : IsSimpleGroup X := e.isSimpleGroup
    refine key ?_ ?_
    · rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2]
      norm_num
    · rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2]
      norm_num
  ·
    obtain ⟨hZ3, ⟨eQ⟩⟩ := htc
    haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := eQ.isSimpleGroup
    have hQcard : Nat.card (X ⧸ Subgroup.center X) = 360 := by
      rw [Nat.card_congr eQ.toEquiv, hA6card]
    have hQperf : Group.IsPerfect (X ⧸ Subgroup.center X) :=
      (isPerfect_center_of_isSimpleGroup inferInstance (by
        rw [hQcard]
        norm_num)).1
    refine ⟨?_, ?_⟩
    · intro N hN h3N
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (N.map (QuotientGroup.mk' (Subgroup.center X))) with hbot | htop
      · have hle : N ≤ Subgroup.center X := by
          have h := (Subgroup.map_eq_bot_iff (H := N)
            (f := QuotientGroup.mk' (Subgroup.center X))).mp hbot
          rwa [QuotientGroup.ker_mk'] at h
        have hdvd : Nat.card N ∣ 3 := by
          rw [← hZ3]
          exact Subgroup.card_dvd_of_le hle
        have hNcard : Nat.card N = 1 := by
          rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
          · exact h
          · exact absurd (h ▸ dvd_rfl) h3N
        exact Subgroup.card_eq_one.mp hNcard
      · exfalso
        have hdvd := Subgroup.card_map_dvd (H := N)
          (f := QuotientGroup.mk' (Subgroup.center X))
        rw [htop, Subgroup.card_top, hQcard] at hdvd
        exact h3N ((by norm_num : (3 : ℕ) ∣ 360).trans hdvd)
    · have hmap := (CFSG.perfect_residual_transport (G := X)
        (f := QuotientGroup.mk' (Subgroup.center X))).1
      have hrange : (QuotientGroup.mk' (Subgroup.center X)).range = ⊤ :=
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
      rw [hrange] at hmap
      haveI : Group.IsPerfect (X ⧸ Subgroup.center X) := hQperf
      have htop : (perfectResidual (⊤ : Subgroup (X ⧸ Subgroup.center X))).map
          (⊤ : Subgroup (X ⧸ Subgroup.center X)).subtype = ⊤ := by
        rw [hresTop inferInstance, Subgroup.map_top, Subgroup.range_subtype]
      rw [htop] at hmap
      have hdvd := Subgroup.card_map_dvd (H := perfectResidual X)
        (f := QuotientGroup.mk' (Subgroup.center X))
      rw [hmap, Subgroup.card_top, hQcard] at hdvd
      exact (by norm_num : (3 : ℕ) ∣ 360).trans hdvd
  ·
    obtain ⟨e⟩ := he
    haveI : IsSimpleGroup X := e.isSimpleGroup
    refine key ?_ ?_
    · rw [Nat.card_congr e.toEquiv, hA5card]
      norm_num
    · rw [Nat.card_congr e.toEquiv, hA5card]
      norm_num

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem case2_type
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h : Ctx A c L d) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (h2 : letI := ker148_normal hY.2; Case148Two A (lB A) Y) :
    ∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
        deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) ∧
      letI := ker148_normal hY.2
      (∀ N : Subgroup ↥(img148 A Y (deltaZero A (lB A) Y)), N.Normal → ¬ 3 ∣ Nat.card N →
          N = ⊥) ∧
        3 ∣ Nat.card (inSubgroup perfectResidual (img148 A Y (deltaZero A (lB A) Y))) := by
  letI := ker148_normal hY.2
  obtain ⟨c', hc', hX, L', hL', hcase⟩ := h2
  refine ⟨c', hc', hX, ?_⟩
  have hHJ : AllPointsHJ A :=
    allPointsHJ_of_j2 h134 h48 h.conf.sec15R.toSec14Std h.conf.j2
  have hJ : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    Wales154.quot_j2_of_allPointsHJ h.conf.sec15R.toSec14Std hHJ hc' hL'
  rcases hcase with h1 | h2case | h3case | h4case
  · obtain ⟨φ⟩ := h1
    have hfacts := type_facts
      (X := ↥(img148 A Y (deltaZero A (lB A) Y))) (Or.inl ⟨φ.trans hJ.some⟩)
    refine ⟨hfacts.1, ?_⟩
    have hcard : Nat.card (inSubgroup perfectResidual (img148 A Y (deltaZero A (lB A) Y))) =
        Nat.card (perfectResidual ↥(img148 A Y (deltaZero A (lB A) Y))) := by
      rw [inSubgroup]
      exact Subgroup.card_map_of_injective (img148 A Y (deltaZero A (lB A) Y)).subtype_injective
    rw [hcard]
    exact hfacts.2
  · obtain ⟨hsmall, -⟩ := h2case
    exfalso
    have hEmpty := Sec17.PropU.isEmpty_equiv_small_of_equiv_J2 hJ
    rcases hsmall with hM22 | hSL | hSU
    · exact hEmpty.2.1.false hM22.some
    · exact (hEmpty.2.2.1 hSL.choose).false hSL.choose_spec.some
    · exact (hEmpty.2.2.2 hSU.choose).false hSU.choose_spec.some
  · obtain ⟨p, f, e, hp, -, -, hiso, -⟩ := h3case
    letI := hp
    exact absurd hiso (Sec17.PropU.not_isoLThreePi_of_equiv_J2 hJ p (f * e))
  · have hfacts := type_facts
      (X := ↥(img148 A Y (deltaZero A (lB A) Y))) (Or.inr h4case.2)
    refine ⟨hfacts.1, ?_⟩
    have hcard : Nat.card (inSubgroup perfectResidual (img148 A Y (deltaZero A (lB A) Y))) =
        Nat.card (perfectResidual ↥(img148 A Y (deltaZero A (lB A) Y))) := by
      rw [inSubgroup]
      exact Subgroup.card_map_of_injective (img148 A Y (deltaZero A (lB A) Y)).subtype_injective
    rw [hcard]
    exact hfacts.2

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
