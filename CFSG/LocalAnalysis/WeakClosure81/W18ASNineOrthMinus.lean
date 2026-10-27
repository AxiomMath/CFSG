module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrth
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthPlus
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusSmall
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
  (finrank_minusSpace_small exists_quadMinus_ne_zero_small nonempty_range_equiv_statedOmega)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.SeitzReduction.F4Pilot (charP_two_of_natCard_eq_two_pow one_le_of_natCard_eq_two_pow)

theorem noSocle185Factor_statedOmega_quadMinus_two (hO : LieOrderFormulasInput) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoSocle185Factor ↥(StatedOmega (StatedQuadMinus 2 F b c)) := by
  have hn : 1 ≤ n := one_le_of_natCard_eq_two_pow hF
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hs, -, hna, hcard, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction (quadMinus 2 F b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 2 F hbc)
      (finrank_minusSpace_small (n := 2) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero_small hbc (by norm_num) U hU)
  obtain ⟨e⟩ := nonempty_range_equiv_statedOmega ρ hcomm
  haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadMinus 2 F b c)) := e.symm.isSimpleGroup
  have hΩ : Nat.card ↥(StatedOmega (StatedQuadMinus 2 F b c)) =
      (2 ^ n) ^ 2 * ((2 ^ n) ^ 4 - 1) := by
    rw [← Nat.card_congr e.toEquiv, hcard, hF]
  have h4 : 4 ≤ 2 ^ (2 * n) :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine NoSocle185Factor.of_isSimpleGroup fun T _ hT => ⟨fun eT => ?_⟩
  have hadm : StatedLieAdmissible .PSL 2 2 (2 * n) :=
    ⟨Nat.prime_two, by omega, le_rfl, fun h => by have := (Prod.mk.inj h).2; omega,
      fun h => by have := (Prod.mk.inj h).2; omega⟩
  have hT' : Nat.card T = (2 ^ n) ^ 2 * ((2 ^ n) ^ 4 - 1) := by
    rw [← Nat.card_congr eT.toEquiv, hΩ]
  have hM : Nat.card T * lieOrderDivisor .PSL 2 (2 ^ (2 * n)) =
      lieOrderNumerator .PSL 2 (2 ^ (2 * n)) := by
    have hq : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [lieOrderDivisor_psl_two_two_pow (by omega), mul_one, hT', hq]
    generalize 2 ^ n = q
    simp only [lieOrderNumerator, Finset.Icc_self, Finset.prod_singleton,
      show 2 * (2 - 1) / 2 = 1 from rfl, pow_one, ← pow_mul]
  rcases hT.crossChar hO hadm hM with ⟨-, -, h2⟩ | ⟨-, h, -⟩ | ⟨h, -⟩
  · obtain rfl : n = 1 := by omega
    have := (hT.card_facts hO).1
    rw [hT'] at this
    norm_num at this
  · omega
  · exact absurd h (by decide)

theorem noSocle185Factor_statedOmega_quadMinus_three (hO : LieOrderFormulasInput) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoSocle185Factor ↥(StatedOmega (StatedQuadMinus 3 F b c)) := by
  have hn : 1 ≤ n := one_le_of_natCard_eq_two_pow hF
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hs, -, hna, hcard, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction (quadMinus 3 F b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 3 F hbc)
      (finrank_minusSpace_small (n := 3) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero_small hbc (by norm_num) U hU)
  obtain ⟨e⟩ := nonempty_range_equiv_statedOmega ρ hcomm
  haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadMinus 3 F b c)) := e.symm.isSimpleGroup
  have hΩ : Nat.card ↥(StatedOmega (StatedQuadMinus 3 F b c)) =
      (2 ^ n) ^ 6 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) := by
    rw [← Nat.card_congr e.toEquiv, hcard, hF]
  refine NoSocle185Factor.of_isSimpleGroup fun T _ hT => ⟨fun eT => ?_⟩
  have hadm : StatedLieAdmissible .PSU 4 2 n :=
    ⟨Nat.prime_two, hn, by norm_num, fun h => by have := (Prod.mk.inj h).1; omega⟩
  have hT' : Nat.card T =
      (2 ^ n) ^ 6 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) := by
    rw [← Nat.card_congr eT.toEquiv, hΩ]
  have hM : Nat.card T * lieOrderDivisor .PSU 4 (2 ^ n) = lieOrderNumerator .PSU 4 (2 ^ n) := by
    rw [lieOrderDivisor_psu_four_two_pow hn, mul_one, hT']
    have h4e : Even (4 : ℕ) := by decide
    have h3e : ¬ Even (3 : ℕ) := by decide
    simp [lieOrderNumerator, show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert, h4e,
      h3e]
    ring
  rcases hT.crossChar hO hadm hM with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h1⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain rfl : n = 1 := h1
    exact (hT.card_facts hO).2.2.2.1 (by rw [hT']; norm_num)

theorem noSocle185Factor_orthogonalMinus_one (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoSocle185Factor ↥(CFSG.PGLModel.orthogonalMinus 1 F b c) :=
  noSocle185Factor_orthogonalMinus_of_statedOmega 1 b c
    (noSocle185Factor_statedOmega_quadMinus_two hO hF hbc)

theorem noSocle185Factor_orthogonalMinus_two (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoSocle185Factor ↥(CFSG.PGLModel.orthogonalMinus 2 F b c) :=
  noSocle185Factor_orthogonalMinus_of_statedOmega 2 b c
    (noSocle185Factor_statedOmega_quadMinus_three hO hF hbc)

theorem noSocle185Factor_of_isOrthGp (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {m n : ℕ} (h : IsOrthGp Y m n) : NoSocle185Factor Y := by
  rcases h with ⟨k, hk, rfl, hY⟩ | ⟨k, hk, rfl, hY⟩
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
    refine NoSocle185Factor.of_mulEquiv e.symm ?_
    rcases (by omega : k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | h4
    · exact noSocle185Factor_orthogonalPlus_two hO hF
    · exact noSocle185Factor_orthogonalPlus_three hO hF
    · exact noSocle185Factor_orthogonalPlus hO hF h4
  · obtain ⟨F, _, _, hF, b, c, hbc, ⟨e⟩⟩ := hY
    refine NoSocle185Factor.of_mulEquiv e.symm ?_
    rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | h3
    · exact noSocle185Factor_orthogonalMinus_one hO hF hbc
    · exact noSocle185Factor_orthogonalMinus_two hO hF hbc
    · exact noSocle185Factor_orthogonalMinus hO hF h3 hbc

end CFSG.LocalAnalysis.WeakClosure81

end
