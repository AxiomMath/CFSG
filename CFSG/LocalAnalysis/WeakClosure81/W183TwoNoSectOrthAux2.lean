module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSectBase
import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSectOrthAux1
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusSmall
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineT

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
  (finrank_minusSpace_small exists_quadMinus_ne_zero_small nonempty_range_equiv_statedOmega)
open CFSG.ComponentClassification.CatLeaf
  (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.SeitzReduction.F4Pilot (charP_two_of_natCard_eq_two_pow one_le_of_natCard_eq_two_pow)

theorem w183b5_noPsp45Factor_statedOmega_quadPlus (hO : LieOrderFormulasInput) {F : Type}
    [Field F] [Finite F] {k n : ℕ} (hF : Nat.card F = 2 ^ n) (hk : 4 ≤ k) :
    NoPsp45Factor ↥(StatedOmega (StatedQuadPlus k F)) := by
  have hadm : StatedLieAdmissible .POmegaPlus k 2 n :=
    ⟨Nat.prime_two, one_le_of_natCard_eq_two_pow hF, hk⟩
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus k F))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (by omega)
  refine w183b5_noPsp45Factor_of_statedProj hO _
    (w183b5_noPsp45Factor_of_lieModel_two hO hadm ?_ ?_)
  · exact Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)

theorem w183b5_noPsp45Factor_statedOmega_quadMinus (hO : LieOrderFormulasInput) {F : Type}
    [Field F] [Finite F] {k n : ℕ} (hF : Nat.card F = 2 ^ n) (hk : 4 ≤ k) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoPsp45Factor ↥(StatedOmega (StatedQuadMinus k F b c)) := by
  have hadm : StatedLieAdmissible .POmegaMinus k 2 n :=
    ⟨Nat.prime_two, one_le_of_natCard_eq_two_pow hF, hk⟩
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus k F b c))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus hk hbc
  refine w183b5_noPsp45Factor_of_statedProj hO _
    (w183b5_noPsp45Factor_of_lieModel_two hO hadm ?_ ?_)
  · exact Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF, b, c, hbc,
      ⟨MulEquiv.refl _⟩⟩
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)

theorem w183b5_noPsp45Factor_orthogonalPlus (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {k n : ℕ} (hF : Nat.card F = 2 ^ n) (hk : 4 ≤ k) :
    NoPsp45Factor ↥(CFSG.PGLModel.orthogonalPlus k F) :=
  w183b5_noPsp45Factor_orthogonalPlus_of_statedOmega hO k
    (w183b5_noPsp45Factor_statedOmega_quadPlus hO hF hk)

theorem w183b5_noPsp45Factor_orthogonalMinus (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {k n : ℕ} (hF : Nat.card F = 2 ^ n) (hk : 3 ≤ k) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoPsp45Factor ↥(CFSG.PGLModel.orthogonalMinus k F b c) :=
  w183b5_noPsp45Factor_orthogonalMinus_of_statedOmega hO k b c
    (w183b5_noPsp45Factor_statedOmega_quadMinus hO hF (by omega) hbc)

theorem w183b5_noPsp45Factor_statedOmega_quadMinus_two (hO : LieOrderFormulasInput) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoPsp45Factor ↥(StatedOmega (StatedQuadMinus 2 F b c)) := by
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
  refine NoPsp45Factor.of_isSimpleGroup fun T _ hT => ⟨fun eT => ?_⟩
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

theorem w183b5_noPsp45Factor_statedOmega_quadMinus_three (hO : LieOrderFormulasInput) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoPsp45Factor ↥(StatedOmega (StatedQuadMinus 3 F b c)) := by
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
  refine NoPsp45Factor.of_isSimpleGroup fun T _ hT => ⟨fun eT => ?_⟩
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

theorem w183b5_noPsp45Factor_orthogonalMinus_one (hO : LieOrderFormulasInput) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoPsp45Factor ↥(CFSG.PGLModel.orthogonalMinus 1 F b c) :=
  w183b5_noPsp45Factor_orthogonalMinus_of_statedOmega hO 1 b c
    (w183b5_noPsp45Factor_statedOmega_quadMinus_two hO hF hbc)

theorem w183b5_noPsp45Factor_orthogonalMinus_two (hO : LieOrderFormulasInput) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoPsp45Factor ↥(CFSG.PGLModel.orthogonalMinus 2 F b c) :=
  w183b5_noPsp45Factor_orthogonalMinus_of_statedOmega hO 2 b c
    (w183b5_noPsp45Factor_statedOmega_quadMinus_three hO hF hbc)

end CFSG.LocalAnalysis.WeakClosure81

end
