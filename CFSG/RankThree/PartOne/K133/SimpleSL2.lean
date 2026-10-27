module

public import CFSG.RankThree.PartOne.K133.KillSporadic
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.RankThree.PartOne.K133

open Matrix

theorem sl2_involution_mem_center {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (hA : A ^ 2 = 1) :
    A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  have hA2 : (A : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hA
    simpa [pow_two] using this
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hA2 0) 0
  have e01 := congrFun (congrFun hA2 0) 1
  have e10 := congrFun (congrFun hA2 1) 0
  have e11 := congrFun (congrFun hA2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  set a := (A : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set b := (A : Matrix (Fin 2) (Fin 2) K) 0 1 with hb
  set c := (A : Matrix (Fin 2) (Fin 2) K) 1 0 with hc
  set d := (A : Matrix (Fin 2) (Fin 2) K) 1 1 with hd
  by_cases hs : a + d = 0
  · exfalso
    apply h2
    have hd' : d = -a := by linear_combination hs
    rw [hd'] at hdet
    linear_combination -hdet - e00
  · have hb0 : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc0 : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hs
    rw [hb0, hc0] at e00 e11 hdet
    have had : a = d := by
      have h1 : a * d = 1 := by linear_combination hdet
      have h2' : a * a = 1 := by linear_combination e00
      have : a * (a - d) = 0 := by linear_combination h2' - h1
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0] at h2'
        simp at h2'
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left ha0)
    refine ⟨a, ?_, ?_⟩
    · have h2' : a * a = 1 := by linear_combination e00
      rw [Fintype.card_fin]
      linear_combination h2'
    · have hb0' : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := hb0
      have hc0' : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hc0
      have had' : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (A : Matrix (Fin 2) (Fin 2) K) 0 0 := had.symm
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, hb0', hc0', had', ha]

theorem false_of_simple_nonabelian_hom_sl2 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {H : Type}
    [Group H] [Finite H] [IsSimpleGroup H] (hne : ∃ a b : H, a * b ≠ b * a)
    (φ : H →* Matrix.SpecialLinearGroup (Fin 2) K) (hφ : Function.Injective φ) : False := by
  classical
  have heven : 2 ∣ Nat.card H := by
    by_contra hodd
    have hodd' : Odd (Nat.card H) := Nat.odd_iff.2 (by omega)
    have hsol := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
    obtain ⟨a, b, hab⟩ := hne
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsol a b)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hφt : φ t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hc := sl2_involution_mem_center h2 (φ t) hφt
  have htc : t ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply hφ
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hc (φ s)
  have hZ := center_eq_bot_of_simple_nonabelian hne
  rw [hZ, Subgroup.mem_bot] at htc
  rw [htc, orderOf_one] at ht
  omega

end CFSG.RankThree.PartOne.K133
