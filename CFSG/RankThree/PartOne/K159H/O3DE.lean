module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.RankThree.PartOne.K159H

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions Module

theorem omega_eq_derived_small {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {Q : QuadraticForm K W} (hQ : (polarBilin Q).Nondegenerate)
    (hd : finrank K W = 4 ∨ finrank K W = 6)
    (hts : ∀ U : Submodule K W, finrank K U = finrank K W / 2 → ∃ u ∈ U, Q u ≠ 0) :
    omegaGroup Q hQ = ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      IsSimpleGroup ↥(omegaGroup Q hQ) ∧ Group.IsPerfect ↥(omegaGroup Q hQ) := by
  obtain ⟨hsimple, hperf, -, hidx, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hQ hd hts
  have hΩO : omegaGroup Q hQ ≤ TauCeti.QuadraticMap.orthogonalGroup Q := omegaGroup_le Q hQ
  have hJΩ : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      omegaGroup Q hQ := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by rcases hd with h | h <;> omega)
  have hmul := Subgroup.relIndex_mul_relIndex
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ (omegaGroup Q hQ)
    (TauCeti.QuadraticMap.orthogonalGroup Q) hJΩ hΩO
  rw [relIndex_omegaGroup Q hQ] at hmul
  have hJO : (⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 := hidx
  have hone : (⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆).relIndex
      (omegaGroup Q hQ) = 1 := by omega
  have hΩJ : omegaGroup Q hQ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    Subgroup.relIndex_eq_one.mp hone
  have heq : omegaGroup Q hQ =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := le_antisymm hΩJ hJΩ
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    exact hsimple
  · rw [heq]
    exact hperf

theorem omega_le_elementary_small {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {Q : QuadraticForm K W} (hQ : (polarBilin Q).Nondegenerate)
    (hd : finrank K W = 4 ∨ finrank K W = 6)
    (hts : ∀ U : Submodule K W, finrank K U = finrank K W / 2 → ∃ u ∈ U, Q u ≠ 0)
    (hE : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hne : ∃ u w, Q u = 0 ∧ polar Q u w = 0 ∧ eichler Q u w ≠ 1) :
    omegaGroup Q hQ ≤ elementaryGroup Q := by
  obtain ⟨hsimple, -, -, hidx, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hQ hd hts
  have hΩO : omegaGroup Q hQ ≤ TauCeti.QuadraticMap.orthogonalGroup Q := omegaGroup_le Q hQ
  have hJΩ : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      omegaGroup Q hQ := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by rcases hd with h | h <;> omega)
  have hmul := Subgroup.relIndex_mul_relIndex
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ (omegaGroup Q hQ)
    (TauCeti.QuadraticMap.orthogonalGroup Q) hJΩ hΩO
  rw [relIndex_omegaGroup Q hQ] at hmul
  have hJO : (⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 := hidx
  have hone : (⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆).relIndex
      (omegaGroup Q hQ) = 1 := by omega
  have hΩJ : omegaGroup Q hQ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    Subgroup.relIndex_eq_one.mp hone
  have hEJ : elementaryGroup Q ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    hE.trans hΩJ
  have hnorm : ((elementaryGroup Q).subgroupOf
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hEJ]
    intro h g hh hg
    exact conj_mem_elementaryGroup (Subgroup.commutator_le_of_le le_rfl le_rfl hg) hh
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ hnorm with hbot | htop
  · exfalso
    obtain ⟨u, w, hu, hw, hne1⟩ := hne
    have hdisj := Subgroup.subgroupOf_eq_bot.mp hbot
    exact hne1 (Subgroup.disjoint_def.mp hdisj (eichler_mem_elementaryGroup Q u w) (hEJ (eichler_mem_elementaryGroup Q u w)))
  · exact hΩJ.trans (Subgroup.subgroupOf_eq_top.mp htop)

end CFSG.RankThree.PartOne.K159H
