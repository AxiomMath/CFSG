module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin

theorem exists_sq_ne_one_of_isPSL_three_two {H : Type} [Group H] {f : ℕ}
    (hH : CFSG.Quasithin.IsPSL 3 2 f H) : ∃ g : H, g ^ 2 ^ 2 = 1 ∧ g ^ 2 ≠ 1 := by
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := hH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  let M : Matrix (Fin 3) (Fin 3) K :=
    1 + Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : K) +
      Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : K)
  have hMdet : M.det = 1 := by
    rw [Matrix.det_fin_three]
    simp [M, Matrix.single, CharTwo.add_self_eq_zero]
  let A : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hMdet]; exact one_ne_zero)
  let N : Matrix (Fin 3) (Fin 3) K := 1 + Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : K)
  have hNdet : N.det = 1 := by
    rw [Matrix.det_fin_three]
    simp [N, Matrix.single, CharTwo.add_self_eq_zero]
  let B : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero N (by rw [hNdet]; exact one_ne_zero)
  have hA2 : A ^ 2 = B := by
    apply Units.ext
    rw [pow_two, Units.val_mul]
    change M * M = N
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, N, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single,
        CharTwo.add_self_eq_zero]
  have hB2 : B * B = 1 := by
    apply Units.ext
    rw [Units.val_mul]
    change N * N = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [N, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single,
        CharTwo.add_self_eq_zero]
  have h4 : A ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, hA2, pow_two, hB2]
  have hnotB : B ∉ CFSG.Open.StatedScalars (Fin 3) K := by
    rintro ⟨u, hu⟩
    have h := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) 0 2) hu
    simp [B, N, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.single] at h
  have hA : A ∈ CFSG.Open.StatedSL 3 K := by
    apply Subgroup.subset_closure
    change M.det = 1
    exact hMdet
  let π : ↥(CFSG.Open.StatedSL 3 K) →* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) :=
    QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin 3) K).subgroupOf
      (CFSG.Open.StatedSL 3 K))
  let x : ↥(CFSG.Open.StatedSL 3 K) := ⟨A, hA⟩
  have hx4 : x ^ 2 ^ 2 = 1 := Subtype.ext h4
  have hπ4 : (π x) ^ 2 ^ 2 = 1 := by
    rw [← map_pow, hx4, map_one]
  have hnotπ2 : (π x) ^ 2 ≠ 1 := by
    intro h2
    have h2' : x ^ 2 ∈ (CFSG.Open.StatedScalars (Fin 3) K).subgroupOf
        (CFSG.Open.StatedSL 3 K) := (QuotientGroup.eq_one_iff _).mp h2
    rw [Subgroup.mem_subgroupOf] at h2'
    apply hnotB
    rw [← hA2]
    simpa using h2'
  let g : H := e.symm (π x)
  refine ⟨g, ?_, ?_⟩
  · calc g ^ 2 ^ 2 = e.symm (π x) ^ 2 ^ 2 := rfl
      _ = e.symm ((π x) ^ 2 ^ 2) := by rw [map_pow]
      _ = 1 := by rw [hπ4, map_one]
  · intro hg2
    apply hnotπ2
    apply e.symm.injective
    rw [map_one]
    calc e.symm ((π x) ^ 2) = (e.symm (π x)) ^ 2 := by rw [map_pow]
      _ = 1 := hg2

end CFSG.Quasithin
