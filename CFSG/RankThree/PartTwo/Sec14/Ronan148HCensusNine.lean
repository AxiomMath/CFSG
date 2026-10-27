module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Open.PGLModelStated
public import CFSG.Open.StatedCenterThree

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Open.StatedCenterThree (cyc3 cyc3GL cyc3GL_mem diagGL diagGL_mem
  eq_of_diagonal_commute_cyc3 exists_orderOf_eq)
open Matrix

section Diagonal

variable {K : Type} [Field K]

theorem diagGL_pow_coe (a : Kˣ) (k : ℕ) :
    ((diagGL a ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(a : K) ^ k, ((a⁻¹ : Kˣ) : K) ^ k, 1] := by
  rw [Units.val_pow_eq_pow_val]
  change (diagonal ![(a : K), ((a⁻¹ : Kˣ) : K), 1]) ^ k = _
  rw [diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagGL_pow_nine (a : Kˣ) (ha : a ^ 9 = 1) : diagGL a ^ 9 = 1 := by
  apply Units.ext
  have h1 : (a : K) ^ 9 = 1 := by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
  have h2 : ((a⁻¹ : Kˣ) : K) ^ 9 = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, ha, inv_one, Units.val_one]
  have hone : (![1, 1, 1] : Fin 3 → K) = 1 := by
    funext i
    fin_cases i <;> simp
  rw [diagGL_pow_coe, Units.val_one, h1, h2, hone, diagonal_one']

theorem pow_three_of_commute_cyc3 (a : Kˣ)
    (h : cyc3GL * diagGL a ^ 3 = diagGL a ^ 3 * cyc3GL) : a ^ 3 = 1 := by
  have hm : cyc3 * ((diagGL a ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((diagGL a ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * cyc3 := by
    have h' := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul] at h'
    exact h'
  rw [diagGL_pow_coe] at hm
  have h2 : (1 : K) = (a : K) ^ 3 := (eq_of_diagonal_commute_cyc3 hm.symm).2
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h2.symm)

end Diagonal

theorem exists_orderOf_nine_projSU_three_eight : ∃ x : projSU 3 2 3, orderOf x = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 2 (2 * 3)) = (2 ^ 3) ^ 2 := by
    rw [GaloisField.card 2 (2 * 3) (by norm_num)]
    norm_num
  obtain ⟨a, ha⟩ := exists_orderOf_eq hK
  have ha9 : a ^ 9 = 1 := by
    have h := pow_orderOf_eq_one a
    rw [ha] at h
    exact h
  have hD : diagGL a ∈ CFSG.Open.StatedSU 3 (2 ^ 3) (GaloisField 2 (2 * 3)) :=
    diagGL_mem (by norm_num) ha9
  have hmem : Matrix.ProjGenLinGroup.mk (diagGL a) ∈ projSU 3 2 3 := by
    rw [← CFSG.PGLModel.projImage_statedSU 3 2 3]
    exact Subgroup.mem_map_of_mem _ hD
  refine ⟨⟨Matrix.ProjGenLinGroup.mk (diagGL a), hmem⟩, ?_⟩
  rw [Subgroup.orderOf_mk]
  have h9 : (Matrix.ProjGenLinGroup.mk (diagGL a)) ^ (3 ^ (1 + 1)) = 1 := by
    show (Matrix.ProjGenLinGroup.mk (diagGL a)) ^ 9 = 1
    rw [← map_pow, diagGL_pow_nine a ha9, map_one]
  have h3 : ¬ (Matrix.ProjGenLinGroup.mk (diagGL a)) ^ 3 = 1 := by
    intro h
    rw [← map_pow, Matrix.ProjGenLinGroup.mk_eq_one, Subgroup.mem_center_iff] at h
    have h3a : a ^ 3 = 1 := pow_three_of_commute_cyc3 a (h cyc3GL)
    have hdvd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one h3a
    rw [ha] at hdvd
    norm_num at hdvd
  have hord : orderOf (Matrix.ProjGenLinGroup.mk (diagGL a)) = 3 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 3) (n := 1) h3 h9
  exact hord.trans (by norm_num)

theorem exists_cube_noncentral_statedSU_three_eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8 ^ 2) :
    ∃ y : CFSG.Assembly.LowTwoRank.StatedSU 3 8 K, y ^ 9 = 1 ∧
      y ^ 3 ∉ Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSU 3 8 K) := by
  obtain ⟨a, ha⟩ := exists_orderOf_eq hK
  have ha9 : a ^ 9 = 1 := by
    have h := pow_orderOf_eq_one a
    rw [ha] at h
    exact h
  have hD : diagGL a ∈ CFSG.Open.StatedSU 3 8 K := diagGL_mem (by norm_num) ha9
  refine ⟨⟨diagGL a, hD⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact diagGL_pow_nine a ha9
  · intro hc
    rw [Subgroup.mem_center_iff] at hc
    have hm : cyc3GL * diagGL a ^ 3 = diagGL a ^ 3 * cyc3GL :=
      congrArg Subtype.val (hc ⟨cyc3GL, cyc3GL_mem (by norm_num)⟩)
    have h3a : a ^ 3 = 1 := pow_three_of_commute_cyc3 a hm
    have hdvd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one h3a
    rw [ha] at hdvd
    norm_num at hdvd

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
