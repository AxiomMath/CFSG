module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofShift
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2Minus

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def KFG2Ord3InvTwo : Prop :=
  ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
    ∀ y : adjointGroup .G2 k, orderOf y = 3 →
      ∃ s : adjointGroup .G2 k, s ≠ 1 ∧ s ^ 2 = 1 ∧ s * y = y * s

namespace Item812Res8

theorem exists_involution_sl2 (K : Type) [Field K] [CharP K 2] :
    ∃ j : SL2 K, j ≠ 1 ∧ j ^ 2 = 1 := by
  have hdet : (Matrix.of ![![(1 : K), 1], ![0, 1]]).det = 1 := by
    simp [Matrix.det_fin_two_of]
  let j : SL2 K := ⟨Matrix.of ![![(1 : K), 1], ![0, 1]], hdet⟩
  have hj : (j : Matrix (Fin 2) (Fin 2) K) = Matrix.of ![![(1 : K), 1], ![0, 1]] := rfl
  refine ⟨j, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp [hj] at h1
  · have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
    ext i k
    rw [Matrix.SpecialLinearGroup.coe_pow, hj]
    fin_cases i <;> fin_cases k <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two, h2]

end Item812Res8


open Sec11.KS11Lie4Proof Item812Res8 in
theorem kFG2Ord3Inv_of
    (hMinus : G2ThreeConjSL2Minus) (h2 : KFG2Ord3InvTwo) : KFG2Ord3Inv := by
  intro m hm k _ _ hk y hy
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    exact h2 k (by rw [hk, pow_one]) y hy
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP k 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hk
    have hk3 : ringChar k ≠ 3 := by rw [ringChar.eq k 2]; norm_num
    have hk4 : 4 ≤ Nat.card k := by
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hy
      omega
    obtain ⟨j₀, hj₀1, hj₀2⟩ := exists_involution_sl2 k
    have key : ∀ g : adjointGroup .G2 k, (∃ j : adjointGroup .G2 k, j ≠ 1 ∧ j ^ 2 = 1 ∧
        j * (g * y * g⁻¹) = (g * y * g⁻¹) * j) →
        ∃ s : adjointGroup .G2 k, s ≠ 1 ∧ s ^ 2 = 1 ∧ s * y = y * s := by
      rintro g ⟨j, hj1, hj2, hjy⟩
      refine ⟨g⁻¹ * j * g, ?_, ?_, ?_⟩
      · intro h
        apply hj1
        calc j = g * (g⁻¹ * j * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
      · rw [show (g⁻¹ * j * g) ^ 2 = g⁻¹ * j ^ 2 * g by rw [sq, sq]; group, hj2]
        group
      · calc g⁻¹ * j * g * y = g⁻¹ * (j * (g * y * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * y * g⁻¹) * j) * g := by rw [hjy]
          _ = y * (g⁻¹ * j * g) := by group
    obtain ⟨g, hgS | hgM⟩ := g2ThreeConjSL2_of_minus hMinus k hk3 hk4 y hy3 hy1
    ·
      obtain ⟨eM⟩ := nonempty_mulEquiv_g2LongSL2 (K := k)
      refine key g ⟨(eM j₀ : adjointGroup .G2 k), ?_, ?_, ?_⟩
      · intro h
        apply hj₀1
        apply eM.injective
        rw [map_one]
        exact Subtype.ext h
      · rw [← Subgroup.coe_pow, ← map_pow, hj₀2, map_one, OneMemClass.coe_one]
      · exact (g2Short_commute_g2Long hgS (eM j₀).2).symm
    ·
      obtain ⟨eS⟩ := nonempty_mulEquiv_g2ShortSL2 (K := k)
      refine key g ⟨(eS j₀ : adjointGroup .G2 k), ?_, ?_, ?_⟩
      · intro h
        apply hj₀1
        apply eS.injective
        rw [map_one]
        exact Subtype.ext h
      · rw [← Subgroup.coe_pow, ← map_pow, hj₀2, map_one, OneMemClass.coe_one]
      · exact g2Short_commute_g2Long (eS j₀).2 hgM

end CFSG.RankThree.PartTwo.Sec8
