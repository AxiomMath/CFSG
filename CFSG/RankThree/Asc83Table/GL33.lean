module

public import CFSG.RankThree.Asc83Table.E9

public section

namespace CFSG.RankThree.Asc83Table

open Subgroup

abbrev GL33 : Type := GL (Fin 3) (ZMod 3)

@[expose] def gl33 (M N : Matrix (Fin 3) (Fin 3) (ZMod 3)) (h₁ : M * N = 1) (h₂ : N * M = 1) :
    GL33 :=
  ⟨M, N, h₁, h₂⟩

@[expose] def t33A : GL33 :=
  gl33 !![1, 0, 1; 0, 1, 0; 0, 0, 1] !![1, 0, 2; 0, 1, 0; 0, 0, 1] (by decide) (by decide)

@[expose] def t33B : GL33 :=
  gl33 !![1, 0, 0; 0, 1, 1; 0, 0, 1] !![1, 0, 0; 0, 1, 2; 0, 0, 1] (by decide) (by decide)

@[expose] def t33C : GL33 :=
  gl33 !![1, 1, 1; 2, 1, 0; 0, 0, 2] !![2, 1, 2; 2, 2, 2; 0, 0, 2] (by decide) (by decide)

theorem t33A_cube : t33A ^ 3 = 1 := by decide +kernel

theorem t33B_cube : t33B ^ 3 = 1 := by decide +kernel

theorem t33A_comm_t33B : Commute t33A t33B := by
  show t33A * t33B = t33B * t33A
  decide +kernel

theorem t33A_ne_one : t33A ≠ 1 := by decide +kernel

theorem t33B_ne_one : t33B ≠ 1 := by decide +kernel

theorem t33B_ne_t33A : t33B ≠ t33A := by decide +kernel

theorem t33B_ne_t33A_sq : t33B ≠ t33A ^ 2 := by decide +kernel

theorem t33C_pow_eight : t33C ^ 8 = 1 := by decide +kernel

theorem t33C_pow_four : t33C ^ 4 ≠ 1 := by decide +kernel

theorem t33C_conj_t33A : t33C * t33A * t33C⁻¹ = t33A ^ 2 * t33B := by decide +kernel

theorem t33C_conj_t33B : t33C * t33B * t33C⁻¹ = t33A ^ 2 * t33B ^ 2 := by decide +kernel

theorem orderOf_t33C : orderOf t33C = 8 :=
  orderOf_eq_prime_pow (p := 2) (n := 2) t33C_pow_four t33C_pow_eight

@[expose] noncomputable def e9t : E9Basis GL33 :=
  E9Basis.ofNe t33A_cube t33B_cube t33A_comm_t33B t33A_ne_one t33B_ne_one t33B_ne_t33A
    t33B_ne_t33A_sq

theorem e9t_a : e9t.a = t33A := rfl

theorem e9t_b : e9t.b = t33B := rfl

theorem e9t_sub : e9t.sub = Subgroup.closure {t33A, t33B} := rfl

theorem t33C_mem_normalizer : t33C ∈ normalizer (e9t.sub : Set GL33) := by
  rw [e9t_sub]
  apply mem_normalizer_closure_of_conj_mem
  rintro s (rfl | rfl)
  · rw [t33C_conj_t33A]
    exact mul_mem (pow_mem (subset_closure (by simp)) _) (subset_closure (by simp))
  · rw [t33C_conj_t33B]
    exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)

theorem closure_le_normalizer :
    Subgroup.closure ({t33A, t33B, t33C} : Set GL33) ≤ normalizer (e9t.sub : Set GL33) := by
  rw [closure_le]
  rintro s (rfl | rfl | rfl)
  · exact le_normalizer (subset_closure (by simp [e9t_a]))
  · exact le_normalizer (subset_closure (by simp [e9t_b]))
  · exact t33C_mem_normalizer

theorem seventy_two_dvd {R : Subgroup GL33} (hA : t33A ∈ R) (hB : t33B ∈ R) (hC : t33C ∈ R) :
    72 ∣ Nat.card R := by
  have h9 : 9 ∣ Nat.card R := by
    have hle : e9t.sub ≤ R := by
      rw [e9t_sub, closure_le]
      rintro s (rfl | rfl)
      · exact hA
      · exact hB
    have := Subgroup.card_dvd_of_le hle
    rwa [show Nat.card e9t.sub = 9 from e9t.card] at this
  have h8 : 8 ∣ Nat.card R := by
    have hle : zpowers t33C ≤ R := Subgroup.zpowers_le.2 hC
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, orderOf_t33C] at this
  exact (show Nat.Coprime 9 8 by norm_num).mul_dvd_of_dvd_of_dvd h9 h8

end CFSG.RankThree.Asc83Table
