module

public import CFSG.GroupTheory.SylowPQMaximal.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.GroupTheory.SylowPQMaximal.Basic
import CFSG.Adapters.SpecialLinearPerfect
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

private lemma factorization_one_twenty_two : (120 : ℕ).factorization 2 = 3 := by
  rw [show (120 : ℕ) = 2 ^ 3 * 15 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (15 : ℕ))]

private lemma classify_dvd_120 {d : ℕ} (hd : d ∣ 120) (h8 : 8 ∣ d) (h3 : ¬ 3 ∣ d) :
    d = 8 ∨ d = 40 ∨ d = 120 := by
  obtain ⟨m, rfl⟩ := h8
  have hm15 : m ∣ 15 := by
    have h : 8 * m ∣ 8 * 15 := by
      rw [show (120 : ℕ) = 8 * 15 by norm_num] at hd
      exact hd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 8)).mp h
  have hm3 : ¬ 3 ∣ m := fun h => h3 (h.mul_left 8)
  have hmle : m ≤ 15 := Nat.le_of_dvd (by norm_num) hm15
  interval_cases m <;> solve | norm_num at hm15 | norm_num at hm3 | norm_num

theorem sylowPQMaximal_specialLinearGroup_two {K : Type*} [Field K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) :
    CFSG.GroupTheory.SylowPQMaximal 2 5 (Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  have hne : Nat.card K ≠ 0 := by rcases hK with h | h <;> omega
  have : Finite K := Nat.finite_of_card_ne_zero hne
  let _ : Fintype K := Fintype.ofFinite K
  have hfcard : Fintype.card K = Nat.card K := Fintype.card_eq_nat_card
  rcases hK with h3 | h5
  · have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 24 := by
      rw [Matrix.card_SL_field, Fin.prod_univ_two, hfcard, h3]
      norm_num
    refine CFSG.GroupTheory.sylowPQMaximal_of_not_dvd (p := 2) (q := 5) ?_
    rw [hcard]
    norm_num
  · have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 120 := by
      rw [Matrix.card_SL_field, Fin.prod_univ_two, hfcard, h5]
      norm_num
    intro P H hPH hH
    have hHpi : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 5 :=
      CFSG.GroupTheory.isPiSubgroup_pair_iff.mp hH
    have hHdvd : Nat.card H ∣ 120 := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card H
    have hPcard : Nat.card (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) = 8 := by
      rw [P.card_eq_multiplicity, hcard, factorization_one_twenty_two]
      norm_num
    have h8dvd : 8 ∣ Nat.card H := by
      rw [← hPcard]
      exact Subgroup.card_dvd_of_le hPH
    have hnot3 : ¬ 3 ∣ Nat.card H := by
      intro h
      rcases hHpi 3 Nat.prime_three h with h' | h' <;> norm_num at h'
    have hHne : H ≠ ⊤ := by
      intro htop
      apply hnot3
      rw [htop, Subgroup.card_top, hcard]
      norm_num
    rcases classify_dvd_120 hHdvd h8dvd hnot3 with h8c | h40c | h120c
    · exact IsPGroup.of_card (p := 2) (n := 3) (by rw [h8c]; norm_num)
    · have hidx : H.index = 3 := by
        have hmul := Subgroup.card_mul_index H
        rw [h40c, hcard] at hmul
        omega
      have hq3 : Nat.card ((Matrix.SpecialLinearGroup (Fin 2) K) ⧸ H) = 3 := by
        rw [← Subgroup.index_eq_card]
        exact hidx
      let act : Matrix.SpecialLinearGroup (Fin 2) K →*
          Equiv.Perm ((Matrix.SpecialLinearGroup (Fin 2) K) ⧸ H) := MulAction.toPermHom _ _
      have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
        CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K (by rw [h5]; norm_num)
      have : Group.IsPerfect act.range := Group.IsPerfect.range act
      have : Group.IsSolvable (Equiv.Perm ((Matrix.SpecialLinearGroup (Fin 2) K) ⧸ H)) :=
        Equiv.Perm.isSolvable (by rw [hq3]; norm_num)
      have : Group.IsSolvable act.range := Group.instIsSolvableSubtypeMemSubgroup act.range
      have hsub : Subsingleton act.range := by
        by_contra h
        have : Nontrivial act.range := not_subsingleton_iff_nontrivial.mp h
        exact Group.IsPerfect.not_isSolvable act.range inferInstance
      have htriv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, act g = 1 := by
        intro g
        have h1 : (⟨act g, ⟨g, rfl⟩⟩ : act.range) = 1 := Subsingleton.elim _ _
        simpa using congrArg Subtype.val h1
      have hcore : H.normalCore = ⊤ := by
        rw [Subgroup.normalCore_eq_ker, eq_top_iff]
        intro g _
        rw [MonoidHom.mem_ker]
        exact htriv g
      exact absurd (top_le_iff.mp (hcore ▸ H.normalCore_le)) hHne
    · exact absurd (Subgroup.eq_top_of_card_eq H (by rw [h120c, hcard])) hHne

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
