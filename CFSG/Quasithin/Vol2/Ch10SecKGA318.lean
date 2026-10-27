module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Open.StatedCenterThree

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Assembly.LowTwoRank Matrix

@[expose] def FactA318ExclTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], A318Case3Group X → Nat.card (Subgroup.center X) = 3

theorem FactA318Excl.two (h : FactA318Excl) : FactA318ExclTwo := h.2

namespace C10KG

variable {K : Type} [Field K]

export CFSG.Open.StatedCenterThree (card_rootsOfUnity_three card_center_statedSL_three
  eq_diagonal_of_commute cyc3 cyc3_mul_transpose transpose_mul_cyc3 cyc3GL
  eq_of_diagonal_commute_cyc3 cyc3GL_mem diagGL diagGL_mem scalar_mem two_le_of_card_eq_sq
  sq_sub_one_eq exists_orderOf_eq card_center_statedSU_three)

theorem det_eq_one_of_mem_statedSU {q : ℕ} {A : GL (Fin 3) K} (hA : A ∈ StatedSU 3 q K) :
    (A : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hA

end C10KG

open C10KG in
theorem factA318ExclTwo_holds : FactA318ExclTwo := by
  intro X _ _ hX
  rcases hX with ⟨s, q, hq, hS⟩ | h6 | h7 | h22
  · cases s
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hS
      have h3 : 3 ∣ q + 1 := by
        have h := Int.ModEq.dvd hq
        simp only [Bool.false_eq_true, ite_false] at h
        omega
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact card_center_statedSU_three hK h3
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hS
      have h3 : 3 ∣ Nat.card K - 1 := by
        have h := Int.ModEq.dvd hq
        simp only [ite_true] at h
        rw [hK]
        omega
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact card_center_statedSL_three h3
  · exact h6.2.1
  · exact h7.2.1
  · exact h22.2.1

end CFSG.Quasithin.Vol2.Ch11.SecA
