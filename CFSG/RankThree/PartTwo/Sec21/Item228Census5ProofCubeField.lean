module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofCube

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Census5Proof

open Matrix CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof

variable {K : Type} [Field K]

theorem no_root_of_card_mod_three [Finite K] (hK3 : Nat.card K % 3 = 2) (s : K) :
    s * s + s + 1 ≠ 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hs3 : s ^ 3 = 1 := by linear_combination (s - 1) * hs
  have hs1 : s ≠ 1 := by
    rintro rfl
    have h3 : (3 : ℕ) • (1 : K) = 0 := by
      rw [nsmul_eq_mul]
      push_cast
      linear_combination hs
    have hord := addOrderOf_eq_prime h3 one_ne_zero
    have hdvd := addOrderOf_dvd_natCard (1 : K)
    rw [hord] at hdvd
    omega
  set u : Kˣ := Units.mk0 s hs0
  have hu : orderOf u = 3 := by
    refine orderOf_eq_prime (Units.ext ?_) (fun h => hs1 ?_)
    · rw [Units.val_pow_eq_pow_val, Units.val_mk0, hs3, Units.val_one]
    · simpa [u] using congrArg Units.val h
  have hdvd := orderOf_dvd_natCard u
  rw [hu, Nat.card_units] at hdvd
  omega

variable (K) in
@[expose] def cubeC : cubeAlg K := ⟨cubeMat K, mem_cubeAlg.mpr rfl⟩

theorem cubeC_sq_add : cubeC K * cubeC K + cubeC K + 1 = 0 :=
  Subtype.ext cubeMat_sq_add

theorem eq_of_pow_three_eq_one (hK : ∀ s : K, s * s + s + 1 ≠ 0) {u : cubeAlg K}
    (hu : u ^ 3 = 1) : u = 1 ∨ u = cubeC K ∨ u = cubeC K * cubeC K := by
  have := (isField_cubeAlg hK).isDomain
  have hC := cubeC_sq_add (K := K)
  have h : (u - 1) * ((u - cubeC K) * (u - cubeC K * cubeC K)) = 0 := by
    linear_combination hu + (-u ^ 2 + cubeC K * u - cubeC K + 1) * hC
  rcases mul_eq_zero.mp h with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  rcases mul_eq_zero.mp h2 with h3 | h4
  · exact Or.inr (Or.inl (sub_eq_zero.mp h3))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h4))

theorem card_units_cubeAlg (hK : ∀ s : K, s * s + s + 1 ≠ 0) :
    Nat.card (cubeAlg K)ˣ = Nat.card K ^ 2 - 1 := by
  let _ : Field (cubeAlg K) := (isField_cubeAlg hK).toField
  rw [← card_cubeAlg]
  exact Nat.card_units _

theorem nonempty_ringEquiv_cubeAlg [Finite K] (hK : ∀ s : K, s * s + s + 1 ≠ 0) (F : Type)
    [Field F] [Finite F] (hF : Nat.card F = Nat.card K ^ 2) : Nonempty (cubeAlg K ≃+* F) := by
  let _ : Field (cubeAlg K) := (isField_cubeAlg hK).toField
  let _ := Fintype.ofFinite (cubeAlg K)
  let _ := Fintype.ofFinite F
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, card_cubeAlg, hF])⟩

end CFSG.RankThree.PartTwo.Sec21.Item228Census5Proof
