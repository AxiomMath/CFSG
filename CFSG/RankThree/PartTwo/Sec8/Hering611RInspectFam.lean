module

public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectArith
public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectRank

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG CFSG.Open
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU StatedSp StatedProj StatedScalars)

variable {X : Type} [Group X] [Finite X] {P : Subgroup X}

theorem false_of_projSU_even {m : ℕ} (hm : Even m) (hm1 : 1 ≤ m) (φ : X ≃* projSU 3 2 m)
    (hP : IsA6Sub P) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * m)) = (2 ^ m) ^ 2 := by
    rw [GaloisField.card 2 (2 * m) (by omega), ← pow_mul, mul_comm]
  have hq : 2 ^ m % 3 = 1 := by
    obtain ⟨k, hk⟩ := hm
    rw [← two_mul] at hk
    rw [hk, pow_mul, Nat.pow_mod]
    norm_num
  have hbot : (StatedScalars (Fin 3) (GaloisField 2 (2 * m))).subgroupOf
      (StatedSU 3 (2 ^ m) (GaloisField 2 (2 * m))) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [(LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num : 1 ≤ 3)).2.2]
    have : Nat.Coprime 3 (2 ^ m + 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    rw [this]
  let e2 : StatedProj (StatedSU 3 (2 ^ m) (GaloisField 2 (2 * m))) ≃*
      StatedSU 3 (2 ^ m) (GaloisField 2 (2 * m)) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact false_of_statedSU_even hm hm1 hK
    ((φ.trans (PGLModel.projSUEquivStatedProj 3 2 m)).trans e2) hP

theorem false_of_statedSU {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 2) (φ : X ≃* StatedSU 3 (2 ^ m) K) (hP : IsA6Sub P) : False := by
  rcases Nat.even_or_odd m with h | h
  · exact false_of_statedSU_even h hm hK φ hP
  · exact false_of_statedSU_odd h hK φ hP

theorem false_of_projSU {m : ℕ} (hm : 1 ≤ m) (φ : X ≃* projSU 3 2 m) (hP : IsA6Sub P) :
    False := by
  rcases Nat.even_or_odd m with h | h
  · exact false_of_projSU_even h hm φ hP
  · exact false_of_projSU_odd h φ hP

theorem false_of_statedSL {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * m)) (φ : X ≃* StatedSL 3 K) (hP : IsA6Sub P) : False :=
  false_of_statedSL_two hK φ hP

end CFSG.RankThree.PartTwo.Sec8.Hering611R
