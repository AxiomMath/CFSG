module

public import CFSG.RankThree.PartOne.FOC.PSLDecomp
import CFSG.LieType.SteinbergBRMulEquivCores
import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.RankThree.PartOne.F106.OddRadGen

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.RankThree.PartOne.FOC Matrix
open scoped commutatorElement

theorem perfectResidual_gl_eq {E : Type} [Field E] {m : ℕ} (hm : 2 ≤ m)
    (hE : 3 ≤ m ∨ ∃ s : Finset E, s.card = 4) :
    perfectResidual (GL (Fin m) E) =
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) E →* GL (Fin m) E).range := by
  apply le_antisymm
  · refine (iInf_le _ 1).trans ?_
    rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro u _ v _
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact Commute.all _ _
  · have hp := CFSG.LinearGroups.special_linear_isPerfect (K := E) (n := m) hm hE
    have : Group.IsPerfect (SpecialLinearGroup (Fin m) E) := hp
    refine CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual _ ?_
    exact Group.IsPerfect.ofSurjective
      (f := (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) E →* GL (Fin m) E).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)

theorem odd_card_rad_perfectResidual_gl {E : Type} [Field E] [Finite E] [CharP E 2] (m : ℕ) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual (GL (Fin m) E)))) := by
  classical
  by_cases hs : Group.IsSolvable (GL (Fin m) E)
  · rw [radical_perfectResidual_eq_bot_of_isSolvable hs, Subgroup.card_bot]
    exact odd_one
  · have hnot : ¬ (m ≤ 1 ∨ (m = 2 ∧ Nat.card E ≤ 3)) := fun h =>
      hs (isSolvable_GL_of_small h)
    have hm : 2 ≤ m := by omega
    have hE : 3 ≤ m ∨ ∃ s : Finset E, s.card = 4 := by
      by_cases h3 : 3 ≤ m
      · exact Or.inl h3
      · right
        have h4 : 4 ≤ Nat.card E := by omega
        have := Fintype.ofFinite E
        have h5 : 4 ≤ (Finset.univ : Finset E).card := by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4
        obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h5
        exact ⟨t, ht⟩
    have hP := perfectResidual_gl_eq (E := E) hm hE
    let e : SpecialLinearGroup (Fin m) E ≃* ↥(perfectResidual (GL (Fin m) E)) :=
      (MonoidHom.ofInjective (SpecialLinearGroup.toGL_injective (n := Fin m) (R := E))).trans
        (MulEquiv.subgroupCongr hP.symm)
    have hq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin m) E) :=
      CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hm hE
    have hq' : CFSG.IsQuasisimple ↥(perfectResidual (GL (Fin m) E)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
    set R := solvableRadical ↥(perfectResidual (GL (Fin m) E)) with hR
    have hRn : R.Normal := inferInstance
    have hRs : Group.IsSolvable R := CFSG.ABGLocalTools.solvableRadical_isSolvable
    have hRc : R ≤ Subgroup.center ↥(perfectResidual (GL (Fin m) E)) := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq' hRn with h | h
      · exfalso
        have hsolv : Group.IsSolvable ↥(perfectResidual (GL (Fin m) E)) := by
          have h1 : Group.IsSolvable ↥(⊤ : Subgroup ↥(perfectResidual (GL (Fin m) E))) := by
            rw [← h]; exact hRs
          exact Group.isSolvable_of_surjective
            (f := (Subgroup.topEquiv (G := ↥(perfectResidual (GL (Fin m) E)))).toMonoidHom)
            (Subgroup.topEquiv (G := ↥(perfectResidual (GL (Fin m) E)))).surjective
        have := CFSG.LocalCores.isQuasisimple_nontrivial hq'
        have := hq'.1
        exact CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect hsolv
      · exact h
    have hRG : R.map (perfectResidual (GL (Fin m) E)).subtype ≤
        (GeneralLinearGroup.scalar (Fin m) : Eˣ →* GL (Fin m) E).range := by
      rintro _ ⟨r, hr, rfl⟩
      rw [← GeneralLinearGroup.center_eq_range_scalar]
      refine mem_center_of_commute_SL _ (fun s => ?_)
      have h1 := Subgroup.mem_center_iff.mp (hRc hr) (e s)
      have h2 := congrArg (fun z : ↥(perfectResidual (GL (Fin m) E)) => (z : GL (Fin m) E)) h1
      exact h2
    have hodd : Odd (Nat.card Eˣ) := by
      have := Fintype.ofFinite E
      have hc := FiniteField.card E 2
      obtain ⟨n, -, hn⟩ := hc
      rw [Nat.card_units, Nat.card_eq_fintype_card]
      have hn' : Fintype.card E = 2 ^ (n : ℕ) := by convert hn
      rw [hn']
      have h2 : 2 ∣ 2 ^ (n : ℕ) := dvd_pow_self 2 n.ne_zero
      have hpos : 0 < 2 ^ (n : ℕ) := by positivity
      obtain ⟨k, hk⟩ := h2
      exact ⟨k - 1, by omega⟩
    have h1 : Nat.card ↥R = Nat.card ↥(R.map (perfectResidual (GL (Fin m) E)).subtype) :=
      (Subgroup.card_map_of_injective (perfectResidual (GL (Fin m) E)).subtype_injective).symm
    rw [h1]
    exact Odd.of_dvd_nat hodd ((Subgroup.card_dvd_of_le hRG).trans (Subgroup.card_range_dvd _))

end CFSG.RankThree.PartOne.F106
