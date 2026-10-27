module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexModelParameter
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open scoped MatrixGroups

universe u

theorem linear_model_borel_parameter {L : Type u} [Group L] [Finite L] {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* PSL(2, GaloisField 2 f)) (B : Subgroup L) (hB : IsBorelSubgroup B) :
    B.index = (2 ^ f) ^ 1 + 1 ∧ Nat.card {x : L // x ∈ B ∧ IsInvolution x} = 2 ^ f - 1 := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 2) (BinaryGaloisField f)) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨ePGL⟩ := psl_charTwo_equiv_pgl f (by omega)
  exact borel_index_and_whole_involution_card_map_mulEquiv
    ((e : L ≃* PSL2BinaryMatrixGroup f).trans ePGL) (2 ^ f) 1
    (fun C hC => linear_borel_index_and_whole_involution_parameter f hf C hC) B hB

theorem suzuki_model_borel_parameter {L : Type u} [Group L] [Finite L] {a : ℕ} (ha : 1 ≤ a)
    (e : L ≃* Sz a) (B : Subgroup L) (hB : IsBorelSubgroup B) :
    B.index = (2 ^ (2 * a + 1)) ^ 2 + 1 ∧
      Nat.card {x : L // x ∈ B ∧ IsInvolution x} = 2 ^ (2 * a + 1) - 1 :=
  borel_index_and_whole_involution_card_map_mulEquiv
    (e.trans (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a)) (2 ^ (2 * a + 1)) 2
    (fun C hC => suzuki_borel_index_and_whole_involution_parameter a ha C hC) B hB

theorem unitary_model_borel_parameter {L : Type u} [Group L] [Finite L] {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* PSU3 2 f) (B : Subgroup L) (hB : IsBorelSubgroup B) :
    B.index = (2 ^ f) ^ 3 + 1 ∧ Nat.card {x : L // x ∈ B ∧ IsInvolution x} = 2 ^ f - 1 := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_injective
    (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
      (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨eJ⟩ := projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let eJ' := eJ.trans (MulEquiv.subgroupCongr hmodel)
  exact borel_index_and_whole_involution_card_map_mulEquiv (e.trans eJ'.symm) (2 ^ f) 3
    (fun C hC => unitary_borel_index_and_whole_involution_parameter J f hf hKcard hfixed hJ
      C hC) B hB

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
