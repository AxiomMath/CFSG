module

import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG

theorem odd_card_radical_perfectResidual_of_odd_card {C : Type*} [Group C] [Finite C]
    (h : Odd (Nat.card C)) : Odd (Nat.card ↥(solvableRadical ↥(perfectResidual C))) := by
  have h1 : Nat.card ↥(solvableRadical ↥(perfectResidual C)) ∣ Nat.card ↥(perfectResidual C) :=
    Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card ↥(perfectResidual C) ∣ Nat.card C := Subgroup.card_subgroup_dvd_card _
  exact Odd.of_dvd_nat h (h1.trans h2)

theorem radical_perfectResidual_eq_bot_of_isSolvable {C : Type*} [Group C] [Finite C]
    (h : Group.IsSolvable C) : solvableRadical ↥(perfectResidual C) = ⊥ := by
  have hperf : Group.IsPerfect ↥(perfectResidual C) :=
    CFSG.Wreathed.PrimewisePerfectLift.perfectResidual_isPerfect
  have hs : Group.IsSolvable ↥(perfectResidual C) :=
    Group.isSolvable_of_isSolvable_injective (f := (perfectResidual C).subtype)
      (perfectResidual C).subtype_injective
  have hsub : Subsingleton ↥(perfectResidual C) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ↥(perfectResidual C) hs
  exact Subgroup.eq_bot_of_subsingleton _

theorem radical_perfectResidual_eq_bot_of_isSimpleGroup {C : Type*} [Group C] [Finite C]
    [IsSimpleGroup C] (hperf : Group.IsPerfect C) :
    solvableRadical ↥(perfectResidual C) = ⊥ := by
  classical
  have htop : perfectResidual C = ⊤ :=
    eq_top_iff.mpr (CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual ⊤
      (Group.IsPerfect.top_iff.mpr hperf))
  let e : ↥(perfectResidual C) ≃* C := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  set R : Subgroup C := (solvableRadical ↥(perfectResidual C)).map e.toMonoidHom with hR
  have hRDn : (solvableRadical ↥(perfectResidual C)).Normal :=
    CFSG.ABGLocalTools.solvableRadical_normal
  have hRn : R.Normal := Subgroup.Normal.map hRDn e.toMonoidHom e.surjective
  have hRs : Group.IsSolvable ↥R := by
    have := CFSG.ABGLocalTools.solvableRadical_isSolvable (H := ↥(perfectResidual C))
    exact Group.isSolvable_of_surjective
      (e.toMonoidHom.subgroupMap_surjective (solvableRadical ↥(perfectResidual C)))
  have hRbot : R = ⊥ := by
    rcases hRn.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hCs : Group.IsSolvable C := by
        have hRs' : Group.IsSolvable ↥(⊤ : Subgroup C) := by rw [← h]; exact hRs
        exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := C)).toMonoidHom)
          (Subgroup.topEquiv (G := C)).surjective
      exact Group.IsPerfect.not_isSolvable C hCs
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hRbot

end CFSG.RankThree.PartOne.F106
