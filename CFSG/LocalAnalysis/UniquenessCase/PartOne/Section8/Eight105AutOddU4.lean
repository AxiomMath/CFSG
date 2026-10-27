module

public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Aut
import CFSG.ClassicalInvolution.RouteD.TypeF4PatternPlane

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.AutOdd

open Matrix Subgroup
open CFSG.LieType.Universal.Unitary (SU mem_SU conjTr antidiag)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply
  unitaryInvolution_involutive)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalInvolution.RouteD.SpAdapt (map_fin_two)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.ClassicalGroups.UnitaryFlag (gramSU mem_gramSU)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Vec d8Vec_mem_SU d8Comb_four)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD torusD_apply shortSL iotaS blkS coe_iotaS
  coe_torusD shortSL_le_SU entry_eq_zero_of_commute card_rootsOfUnity_three
  eq_one_or_eq_or_eq_inv unitaryInvolution_rootsOfUnity antidiag_four)

variable {F : Type} [Field F]

theorem entry_eq_zero_of_mul_diagonal {g : Matrix (Fin 4) (Fin 4) F} {d d' : Fin 4 → F}
    (h : g * diagonal d' = diagonal d * g) {i j : Fin 4} (hij : d i ≠ d' j) : g i j = 0 := by
  have e := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at e
  have e' : (d' j - d i) * g i j = 0 := by linear_combination e
  rcases mul_eq_zero.mp e' with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hij
  · exact h0

theorem eq_smul_one_and_eq_of_mul_specialSL {X : Matrix (Fin 2) (Fin 2) F} {τ τ' : F} (hX : X ≠ 0)
    (h12 : X * (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * X)
    (h21 : X * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * X)
    (hτ : X * (!![τ', 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) =
      (!![τ, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * X) :
    X 0 0 ≠ 0 ∧ X = X 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) ∧ τ' = τ := by
  have h10 : X 1 0 = 0 := by
    have e := congrFun (congrFun h12 0) 0
    rw [(Matrix.two_mul_expl X (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F)).1,
      (Matrix.two_mul_expl (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) X).1] at e
    simpa using e
  have h0011 : X 0 0 = X 1 1 := by
    have e := congrFun (congrFun h12 0) 1
    rw [(Matrix.two_mul_expl X (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F)).2.1,
      (Matrix.two_mul_expl (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) X).2.1] at e
    simp at e
    linear_combination e
  have h01 : X 0 1 = 0 := by
    have e := congrFun (congrFun h21 0) 0
    rw [(Matrix.two_mul_expl X (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F)).1,
      (Matrix.two_mul_expl (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) X).1] at e
    simpa using e
  have hX0 : X 0 0 ≠ 0 := by
    rintro h0
    refine hX ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  refine ⟨hX0, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h0011]
  · have e := congrFun (congrFun hτ 0) 0
    rw [(Matrix.two_mul_expl X (!![τ', 1; 1, 0] : Matrix (Fin 2) (Fin 2) F)).1,
      (Matrix.two_mul_expl (!![τ, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) X).1] at e
    simp [h01, h10] at e
    exact mul_left_cancel₀ hX0 (by rw [e, mul_comm])

theorem eq_diagonal_of_eq_smul_one {S : Matrix (Fin 4) (Fin 4) F} {lam mu : F}
    (hY : (!![S 0 0, S 0 1; S 1 0, S 1 1] : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hW : (!![S 2 2, S 2 3; S 3 2, S 3 3] : Matrix (Fin 2) (Fin 2) F) = mu • 1)
    (h02 : S 0 2 = 0) (h03 : S 0 3 = 0) (h12 : S 1 2 = 0) (h13 : S 1 3 = 0)
    (h20 : S 2 0 = 0) (h21 : S 2 1 = 0) (h30 : S 3 0 = 0) (h31 : S 3 1 = 0) :
    S = diagonal ![lam, lam, mu, mu] := by
  have h00 : S 0 0 = lam := by simpa using congrFun (congrFun hY 0) 0
  have h01 : S 0 1 = 0 := by simpa using congrFun (congrFun hY 0) 1
  have h10 : S 1 0 = 0 := by simpa using congrFun (congrFun hY 1) 0
  have h11 : S 1 1 = lam := by simpa using congrFun (congrFun hY 1) 1
  have h22 : S 2 2 = mu := by simpa using congrFun (congrFun hW 0) 0
  have h23 : S 2 3 = 0 := by simpa using congrFun (congrFun hW 0) 1
  have h32 : S 3 2 = 0 := by simpa using congrFun (congrFun hW 1) 0
  have h33 : S 3 3 = mu := by simpa using congrFun (congrFun hW 1) 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, h00, h01, h10, h11, h22, h23, h32, h33, h02, h03, h12, h13,
      h20, h21, h30, h31]

theorem diagBlocks_mul_of_mul_blkS {σ : F ≃+* F} {S : Matrix (Fin 4) (Fin 4) F} {ψ : F →+* F}
    {B B' : Matrix (Fin 2) (Fin 2) F} (hB' : B' = B.map σ)
    (h02 : S 0 2 = 0) (h03 : S 0 3 = 0) (h12 : S 1 2 = 0) (h13 : S 1 3 = 0)
    (h20 : S 2 0 = 0) (h21 : S 2 1 = 0) (h30 : S 3 0 = 0) (h31 : S 3 1 = 0)
    (h : S * (blkS σ B).map ψ = blkS σ B * S) :
    (!![S 0 0, S 0 1; S 1 0, S 1 1] * B.map ψ = B * !![S 0 0, S 0 1; S 1 0, S 1 1]) ∧
      (!![S 2 2, S 2 3; S 3 2, S 3 3] * B'.map ψ =
        B' * !![S 2 2, S 2 3; S 3 2, S 3 3]) := by
  have T00 := congrFun (congrFun h 0) 0
  have T01 := congrFun (congrFun h 0) 1
  have T10 := congrFun (congrFun h 1) 0
  have T11 := congrFun (congrFun h 1) 1
  have L00 := congrFun (congrFun h 2) 2
  have L01 := congrFun (congrFun h 2) 3
  have L10 := congrFun (congrFun h 3) 2
  have L11 := congrFun (congrFun h 3) 3
  simp only [Matrix.mul_apply, Fin.sum_univ_four] at T00 T01 T10 T11 L00 L01 L10 L11
  simp [Matrix.map_apply, h02, h03, h12, h13, h20, h21, h30, h31, blkS]
    at T00 T01 T10 T11 L00 L01 L10 L11
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS] using T00
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS] using T01
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS] using T10
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS] using T11
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS, hB'] using L00
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS, hB'] using L01
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS, hB'] using L10
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS, hB'] using L11

theorem offDiagBlocks_mul_of_mul_blkS {σ : F ≃+* F} {S : Matrix (Fin 4) (Fin 4) F} {ψ : F →+* F}
    {B B' : Matrix (Fin 2) (Fin 2) F} (hB' : B' = B.map σ)
    (h00 : S 0 0 = 0) (h01 : S 0 1 = 0) (h10 : S 1 0 = 0) (h11 : S 1 1 = 0)
    (h : S * (blkS σ B).map ψ = blkS σ B * S) :
    !![S 0 2, S 0 3; S 1 2, S 1 3] * B'.map ψ = B * !![S 0 2, S 0 3; S 1 2, S 1 3] := by
  have T00 := congrFun (congrFun h 0) 2
  have T01 := congrFun (congrFun h 0) 3
  have T10 := congrFun (congrFun h 1) 2
  have T11 := congrFun (congrFun h 1) 3
  simp only [Matrix.mul_apply, Fin.sum_univ_four] at T00 T01 T10 T11
  simp [Matrix.map_apply, h00, h01, h10, h11, blkS] at T00 T01 T10 T11
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS, hB'] using T00
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS, hB'] using T01
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS, hB'] using T10
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, blkS, hB'] using T11

theorem diagBlocks_mul_of_commute_blkS {σ : F ≃+* F} {S : Matrix (Fin 4) (Fin 4) F} {ψ : F →+* F}
    (h02 : S 0 2 = 0) (h03 : S 0 3 = 0) (h12 : S 1 2 = 0) (h13 : S 1 3 = 0)
    (h20 : S 2 0 = 0) (h21 : S 2 1 = 0) (h30 : S 3 0 = 0) (h31 : S 3 1 = 0)
    (hK : ∀ (B : Matrix (Fin 2) (Fin 2) F), B.det = 1 →
      S * (blkS σ B).map ψ = blkS σ B * S) :
    ∀ (B B' : Matrix (Fin 2) (Fin 2) F), B' = B.map σ → B.det = 1 →
      (!![S 0 0, S 0 1; S 1 0, S 1 1] * B.map ψ = B * !![S 0 0, S 0 1; S 1 0, S 1 1]) ∧
        (!![S 2 2, S 2 3; S 3 2, S 3 3] * B'.map ψ =
          B' * !![S 2 2, S 2 3; S 3 2, S 3 3]) := by
  intro B B' hB' hB
  exact diagBlocks_mul_of_mul_blkS hB' h02 h03 h12 h13 h20 h21 h30 h31 (hK B hB)

theorem eq_one_of_diagBlocks_relations {Y : Matrix (Fin 2) (Fin 2) F} {ψ : F ≃+* F} (hY : Y ≠ 0)
    (h12 : Y * (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * Y)
    (h21 : Y * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * Y)
    (hτ : ∀ τ : F, Y * (!![ψ τ, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) =
      (!![τ, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * Y) :
    ψ = 1 :=
  RingEquiv.ext fun τ => (eq_smul_one_and_eq_of_mul_specialSL hY h12 h21 (hτ τ)).2.2

theorem exists_eq_smul_one_of_diagBlocks_relations {Y : Matrix (Fin 2) (Fin 2) F} (hY : Y ≠ 0)
    (h12 : Y * (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * Y)
    (h21 : Y * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * Y)
    (h0 : Y * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * Y) :
    ∃ lam : F, lam ≠ 0 ∧ Y = lam • (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨hne, hsmul, -⟩ := eq_smul_one_and_eq_of_mul_specialSL hY h12 h21 h0
  exact ⟨Y 0 0, hne, hsmul⟩

theorem diagBlocks_ne_zero {S : Matrix (Fin 4) (Fin 4) F} (hSdet : S.det ≠ 0)
    (h02 : S 0 2 = 0) (h03 : S 0 3 = 0) (h20 : S 2 0 = 0) (h21 : S 2 1 = 0) :
    (!![S 0 0, S 0 1; S 1 0, S 1 1] : Matrix (Fin 2) (Fin 2) F) ≠ 0 ∧
      (!![S 2 2, S 2 3; S 3 2, S 3 3] : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rintro h0
    have e0 : S 0 0 = 0 := by simpa using congrFun (congrFun h0 0) 0
    have e1 : S 0 1 = 0 := by simpa using congrFun (congrFun h0 0) 1
    exact hSdet (Matrix.det_eq_zero_of_row_eq_zero 0 fun j => by
      fin_cases j <;> simp [e0, e1, h02, h03])
  · rintro h0
    have e0 : S 2 2 = 0 := by simpa using congrFun (congrFun h0 0) 0
    have e1 : S 2 3 = 0 := by simpa using congrFun (congrFun h0 0) 1
    exact hSdet (Matrix.det_eq_zero_of_row_eq_zero 2 fun j => by
      fin_cases j <;> simp [e0, e1, h20, h21])

theorem ne_zero_of_upperRight_block {S : Matrix (Fin 4) (Fin 4) F} (hSdet : S.det ≠ 0)
    (h00 : S 0 0 = 0) (h01 : S 0 1 = 0) :
    (!![S 0 2, S 0 3; S 1 2, S 1 3] : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
  rintro h0
  have e0 : S 0 2 = 0 := by simpa using congrFun (congrFun h0 0) 0
  have e1 : S 0 3 = 0 := by simpa using congrFun (congrFun h0 0) 1
  exact hSdet (Matrix.det_eq_zero_of_row_eq_zero 0 fun j => by
    fin_cases j <;> simp [e0, e1, h00, h01])

theorem pow_three_and_ne_of_rootsOfUnity {a : F} {ω : rootsOfUnity 3 F}
    (ha : a = ((ω : Fˣ) : F)) (hω : ω ≠ 1) :
    a ^ 3 = 1 ∧ a ≠ 0 ∧ a ≠ 1 ∧ a ≠ a⁻¹ := by
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at ha3
    norm_num at ha3
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext (by rw [← ha]; exact h)))
  refine ⟨ha3, ha0, ha1, fun h => ha1 ?_⟩
  have h2 : a ^ 2 = 1 := by
    rw [pow_two, congrArg (fun x => a * x) h, mul_inv_cancel₀ ha0]
  have h4 : a ^ 3 = a ^ 2 * a := by ring
  rw [h4, h2, one_mul] at ha3
  exact ha3

theorem fieldAut_apply_eq_or_eq_inv (hcard : Nat.card (rootsOfUnity 3 F) = 3)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) (ψ : F ≃+* F) :
    ψ ((ω : Fˣ) : F) = ((ω : Fˣ) : F) ∨ ψ ((ω : Fˣ) : F) = (((ω : Fˣ) : F))⁻¹ := by
  have ha3 : ((ω : Fˣ) : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have hψ3 : ψ ((ω : Fˣ) : F) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hcoe : (((rootsOfUnity.mkOfPowEq (ψ ((ω : Fˣ) : F)) hψ3 : rootsOfUnity 3 F) : Fˣ) : F) =
      ψ ((ω : Fˣ) : F) := rootsOfUnity.coe_mkOfPowEq hψ3
  rcases eq_one_or_eq_or_eq_inv hcard hω
    (rootsOfUnity.mkOfPowEq (ψ ((ω : Fˣ) : F)) hψ3) with h1 | h1 | h1
  · exfalso
    have hψ1 : ψ ((ω : Fˣ) : F) = 1 := by rw [← hcoe, h1]; rfl
    have hA1 : ((ω : Fˣ) : F) = 1 := ψ.injective (by rw [hψ1, map_one])
    exact hω (Subtype.ext (Units.ext hA1))
  · left
    rw [← hcoe, h1]
  · right
    rw [← hcoe, h1, Subgroup.coe_inv, Units.val_inv_eq_inv_val]

theorem offDiagBlocks_eq_zero_of_commute_torusD {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    {ψ : F ≃+* F} {S : Matrix (Fin 4) (Fin 4) F}
    (hψa : ψ ((ω : Fˣ) : F) = ((ω : Fˣ) : F))
    (hT : S * (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F).map ψ =
      (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) * S) :
    S 0 2 = 0 ∧ S 0 3 = 0 ∧ S 1 2 = 0 ∧ S 1 3 = 0 ∧ S 2 0 = 0 ∧ S 2 1 = 0 ∧ S 3 0 = 0 ∧
      S 3 1 = 0 := by
  set a : F := ((ω : Fˣ) : F) with ha
  obtain ⟨-, -, -, hainv⟩ := pow_three_and_ne_of_rootsOfUnity ha hω
  have hψa' : ψ a = a := by rw [ha]; exact hψa
  have ht₀coe : (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [coe_torusD]
    simp only [ha, Units.val_inv_eq_inv_val]
  have ht₀map : (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) :
      Matrix (Fin 4) (Fin 4) F).map ψ = diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [ht₀coe, Matrix.diagonal_map (map_zero ψ)]
    congr 1
    funext i
    fin_cases i <;> simp [hψa', map_inv₀]
  have hst : S * diagonal ![a, a, a⁻¹, a⁻¹] = diagonal ![a, a, a⁻¹, a⁻¹] * S := by
    have h := hT
    rw [ht₀map, ht₀coe] at h
    exact h
  exact ⟨entry_eq_zero_of_commute hst (by simpa using hainv),
    entry_eq_zero_of_commute hst (by simpa using hainv),
    entry_eq_zero_of_commute hst (by simpa using hainv),
    entry_eq_zero_of_commute hst (by simpa using hainv),
    entry_eq_zero_of_commute hst (by simpa using hainv.symm),
    entry_eq_zero_of_commute hst (by simpa using hainv.symm),
    entry_eq_zero_of_commute hst (by simpa using hainv.symm),
    entry_eq_zero_of_commute hst (by simpa using hainv.symm)⟩

theorem upperBlocks_eq_zero_of_commute_torusD_inv {ω : rootsOfUnity 3 F}
    (hω : ω ≠ 1) {ψ : F ≃+* F} {S : Matrix (Fin 4) (Fin 4) F}
    (hψa : ψ ((ω : Fˣ) : F) = (((ω : Fˣ) : F))⁻¹)
    (hT : S * (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F).map ψ =
      (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) * S) :
    S 0 0 = 0 ∧ S 0 1 = 0 ∧ S 1 0 = 0 ∧ S 1 1 = 0 := by
  set a : F := ((ω : Fˣ) : F) with ha
  obtain ⟨-, -, -, hainv⟩ := pow_three_and_ne_of_rootsOfUnity ha hω
  have hψa' : ψ a = a⁻¹ := by rw [ha]; exact hψa
  have ht₀coe : (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [coe_torusD]
    simp only [ha, Units.val_inv_eq_inv_val]
  have ht₀map : (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) :
      Matrix (Fin 4) (Fin 4) F).map ψ = diagonal ![a⁻¹, a⁻¹, a, a] := by
    rw [ht₀coe, Matrix.diagonal_map (map_zero ψ)]
    congr 1
    funext i
    fin_cases i <;> simp [hψa', map_inv₀]
  have hst : S * diagonal ![a⁻¹, a⁻¹, a, a] = diagonal ![a, a, a⁻¹, a⁻¹] * S := by
    have h := hT
    rw [ht₀map, ht₀coe] at h
    exact h
  exact ⟨entry_eq_zero_of_mul_diagonal hst (by simpa using hainv),
    entry_eq_zero_of_mul_diagonal hst (by simpa using hainv),
    entry_eq_zero_of_mul_diagonal hst (by simpa using hainv),
    entry_eq_zero_of_mul_diagonal hst (by simpa using hainv)⟩

variable [Finite F]

theorem diagonal_pow_card_sub_one {lam mu : F} (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) :
    (diagonal ![lam, lam, mu, mu] : Matrix (Fin 4) (Fin 4) F) ^ (Nat.card F - 1) = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have hlam : lam ^ (Nat.card F - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one lam hlam0
  have hmu : mu ^ (Nat.card F - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one mu hmu0
  rw [Matrix.diagonal_pow]
  have h1 : ((![lam, lam, mu, mu] : Fin 4 → F) ^ (Nat.card F - 1)) = 1 := by
    funext i
    fin_cases i
    · simpa using hlam
    · simpa using hlam
    · simpa using hmu
    · simpa using hmu
  rw [h1]
  simp

variable [CharP F 2] {b : ℕ}

omit [CharP F 2] in
theorem one_le_of_card_eq_two_pow_sq (hF : Nat.card F = (2 ^ b) ^ 2) : 1 ≤ b := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    exfalso
    have : Fintype F := Fintype.ofFinite F
    have h2 : 1 < Fintype.card F := Fintype.one_lt_card
    rw [← Nat.card_eq_fintype_card, hF] at h2
    simp at h2
  · exact hb

omit [CharP F 2] in
theorem odd_card_sub_one (hF : Nat.card F = (2 ^ b) ^ 2) : Odd (Nat.card F - 1) := by
  have hb1 : 1 ≤ b := one_le_of_card_eq_two_pow_sq hF
  rw [hF, ← pow_mul, Nat.mul_comm b 2]
  have hpos : 0 < 2 ^ (2 * b - 1) := pow_pos (by norm_num) _
  have h2 : 2 ^ (2 * b) = 2 * 2 ^ (2 * b - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)]
  exact ⟨2 ^ (2 * b - 1) - 1, by omega⟩

omit [CharP F 2] in
theorem coprime_two_pow_card_sub_one (hF : Nat.card F = (2 ^ b) ^ 2) (k : ℕ) :
    Nat.Coprime (2 ^ k) (Nat.card F - 1) :=
  (odd_card_sub_one hF).coprime_two_left.pow_left k

theorem su_eq_gramSU_miyamotoJ4 (hdata : UnitaryFieldData 2 b F) :
    SU (unitaryInvolution F 2 b) 4 = gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F) := by
  have hbar : ∀ M : Matrix (Fin 4) (Fin 4) F,
      M.map (unitaryInvolution F 2 b) = M.map hdata.bar := by
    intro M
    ext i j
    simp only [Matrix.map_apply, hdata.bar_apply, unitaryInvolution_apply]
  have hJ : (antidiag 4 : Matrix (Fin 4) (Fin 4) F) = CFSG.LocalAnalysis.miyamotoJ4 F := by
    rw [antidiag_four, CFSG.LocalAnalysis.miyamotoJ4]
  ext g
  rw [mem_SU, mem_gramSU, hJ]
  simp only [conjTr, hbar]
  exact and_comm

omit [Finite F] [CharP F 2] in
theorem coe_eq_mul_glAut_mul_inv {hdata : UnitaryFieldData 2 b F}
    {β : MulAut (gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F))}
    {s : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F)} {ψ : F ≃+* F}
    (hβ : β = MulAut.conj s * CFSG.LocalAnalysis.EvenBN.U4.miyamotoFieldAut hdata ψ)
    (g : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F)) :
    ((β g : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F)) : GL (Fin 4) F) =
      s * glAut ψ (g : GL (Fin 4) F) * s⁻¹ := by
  rw [hβ, MulAut.mul_apply, MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv,
    CFSG.LocalAnalysis.EvenBN.U4.coe_miyamotoFieldAut_apply]

omit [Finite F] [CharP F 2] in
theorem mul_glAut_eq_mul_of_fixed {hdata : UnitaryFieldData 2 b F}
    {β : MulAut (gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F))}
    {s : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F)} {ψ : F ≃+* F}
    (hform : ∀ g : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F),
      ((β g : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F)) : GL (Fin 4) F) =
        s * glAut ψ (g : GL (Fin 4) F) * s⁻¹)
    {g : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F)} (hx : β g = g) :
    ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (((g : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F).map ψ =
      (((g : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) *
        ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  have h2 := hform g
  rw [hx] at h2
  simp only [Subgroup.coe_inv] at h2
  have h4 : (s : GL (Fin 4) F) * glAut ψ (g : GL (Fin 4) F) =
      (g : GL (Fin 4) F) * (s : GL (Fin 4) F) := by
    have h6 : (g : GL (Fin 4) F) * (s : GL (Fin 4) F) =
        (s : GL (Fin 4) F) * glAut ψ (g : GL (Fin 4) F) := by
      calc (g : GL (Fin 4) F) * (s : GL (Fin 4) F)
          = ((s : GL (Fin 4) F) * glAut ψ (g : GL (Fin 4) F) * (s : GL (Fin 4) F)⁻¹) *
              (s : GL (Fin 4) F) := by conv_lhs => rw [h2]
        _ = (s : GL (Fin 4) F) * glAut ψ (g : GL (Fin 4) F) := by group
    rw [h6]
  have h5 := congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) h4
  simpa only [Units.val_mul, coe_glAut] using h5

theorem fixed_relations {hdata : UnitaryFieldData 2 b F}
    {hSU : SU (unitaryInvolution F 2 b) 4 = gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F)}
    {α : MulAut ↥(SU (unitaryInvolution F 2 b) 4)}
    {β : MulAut (gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F))}
    {s : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F)} {ψ : F ≃+* F}
    (hform : ∀ g : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F),
      ((β g : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F)) : GL (Fin 4) F) =
        s * glAut ψ (g : GL (Fin 4) F) * s⁻¹)
    (hcongr : ∀ x : ↥(SU (unitaryInvolution F 2 b) 4),
      β (MulEquiv.subgroupCongr hSU x) = MulEquiv.subgroupCongr hSU (α x))
    {ω : rootsOfUnity 3 F} (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2)
    (hK : ∀ x : ↥(SU (unitaryInvolution F 2 b) 4),
      (x : GL (Fin 4) F) ∈ shortSL (unitaryInvolution F 2 b) → α x = x)
    (ht : ∀ x : ↥(SU (unitaryInvolution F 2 b) 4),
      (x : GL (Fin 4) F) = torusD ((ω, ω) : D8Mod 3 F) → α x = x) :
    (∀ (B : Matrix (Fin 2) (Fin 2) F), B.det = 1 →
      ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (blkS (unitaryInvolution F 2 b) B).map ψ =
        blkS (unitaryInvolution F 2 b) B * ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) ∧
      (((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F).map ψ =
        (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) *
          ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
  refine ⟨fun B hB => ?_, ?_⟩
  · have hkSL : iotaS (unitaryInvolution F 2 b) ⟨B, hB⟩ ∈ shortSL (unitaryInvolution F 2 b) :=
      ⟨⟨B, hB⟩, rfl⟩
    have hkSU : iotaS (unitaryInvolution F 2 b) ⟨B, hB⟩ ∈ SU (unitaryInvolution F 2 b) 4 :=
      shortSL_le_SU (unitaryInvolution F 2 b) (unitaryInvolution_involutive hF) hkSL
    have hx : β (MulEquiv.subgroupCongr hSU ⟨_, hkSU⟩) =
        MulEquiv.subgroupCongr hSU ⟨_, hkSU⟩ := by
      rw [hcongr, hK _ hkSL]
    exact mul_glAut_eq_mul_of_fixed hform hx
  · set k : GL (Fin 4) F := torusD ((ω, ω) : D8Mod 3 F) with hkdef
    have hkSU : k ∈ SU (unitaryInvolution F 2 b) 4 := by
      rw [hkdef, torusD_apply]
      exact d8Vec_mem_SU (Or.inl rfl) d8Comb_four _
        (fun u => unitaryInvolution_rootsOfUnity hbe u) _
    have hx : β (MulEquiv.subgroupCongr hSU ⟨k, hkSU⟩) =
        MulEquiv.subgroupCongr hSU ⟨k, hkSU⟩ := by
      rw [hcongr, ht ⟨k, hkSU⟩ (by simp [hkdef])]
    exact mul_glAut_eq_mul_of_fixed hform hx

theorem diagBlocks_relations {S : Matrix (Fin 4) (Fin 4) F} {ψ : F ≃+* F}
    (h02 : S 0 2 = 0) (h03 : S 0 3 = 0) (h12 : S 1 2 = 0) (h13 : S 1 3 = 0)
    (h20 : S 2 0 = 0) (h21 : S 2 1 = 0) (h30 : S 3 0 = 0) (h31 : S 3 1 = 0)
    (hK : ∀ (B : Matrix (Fin 2) (Fin 2) F), B.det = 1 →
      S * (blkS (unitaryInvolution F 2 b) B).map ψ = blkS (unitaryInvolution F 2 b) B * S) :
    (!![S 0 0, S 0 1; S 1 0, S 1 1] : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1] =
        !![1, 1; 0, 1] * !![S 0 0, S 0 1; S 1 0, S 1 1] ∧
      (!![S 0 0, S 0 1; S 1 0, S 1 1] : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1] =
        !![1, 0; 1, 1] * !![S 0 0, S 0 1; S 1 0, S 1 1] ∧
      (∀ τ : F, (!![S 0 0, S 0 1; S 1 0, S 1 1] : Matrix (Fin 2) (Fin 2) F) * !![ψ τ, 1; 1, 0] =
        !![τ, 1; 1, 0] * !![S 0 0, S 0 1; S 1 0, S 1 1]) ∧
    (!![S 2 2, S 2 3; S 3 2, S 3 3] : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1] =
        !![1, 1; 0, 1] * !![S 2 2, S 2 3; S 3 2, S 3 3] ∧
      (!![S 2 2, S 2 3; S 3 2, S 3 3] : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1] =
        !![1, 0; 1, 1] * !![S 2 2, S 2 3; S 3 2, S 3 3] ∧
      (!![S 2 2, S 2 3; S 3 2, S 3 3] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0] =
        !![0, 1; 1, 0] * !![S 2 2, S 2 3; S 3 2, S 3 3] := by
  have hblk := diagBlocks_mul_of_commute_blkS (σ := unitaryInvolution F 2 b)
    (ψ := (ψ : F →+* F)) h02 h03 h12 h13 h20 h21 h30 h31 hK
  have mapE12 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).map (unitaryInvolution F 2 b) := by
    rw [map_fin_two]; simp
  have mapE21 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F).map (unitaryInvolution F 2 b) := by
    rw [map_fin_two]; simp
  have mapB0 : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).map (unitaryInvolution F 2 b) := by
    rw [map_fin_two]; simp
  have detE12 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two]; norm_num
  have detE21 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two]; norm_num
  have detB : ∀ τ : F, (!![τ, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    intro τ
    rw [Matrix.det_fin_two]
    simp [CharTwo.neg_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [map_fin_two] using (hblk _ _ mapE12 detE12).1
  · simpa [map_fin_two] using (hblk _ _ mapE21 detE21).1
  · intro τ
    simpa [map_fin_two] using (hblk _ _ (by rw [map_fin_two]) (detB τ)).1
  · simpa [map_fin_two] using (hblk _ _ mapE12 detE12).2
  · simpa [map_fin_two] using (hblk _ _ mapE21 detE21).2
  · simpa [map_fin_two] using (hblk _ _ mapB0 (detB 0)).2

theorem eq_one_and_pow_of_fix_blkS {ω : rootsOfUnity 3 F}
    (hω : ω ≠ 1) {ψ : F ≃+* F} {S : Matrix (Fin 4) (Fin 4) F}
    (hSdet : S.det ≠ 0) (hψa : ψ ((ω : Fˣ) : F) = ((ω : Fˣ) : F))
    (hK : ∀ (B : Matrix (Fin 2) (Fin 2) F), B.det = 1 →
      S * (blkS (unitaryInvolution F 2 b) B).map ψ = blkS (unitaryInvolution F 2 b) B * S)
    (hT : S * (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F).map ψ =
      (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) * S) :
    ψ = 1 ∧ S ^ (Nat.card F - 1) = 1 := by
  obtain ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩ :=
    offDiagBlocks_eq_zero_of_commute_torusD hω hψa hT
  obtain ⟨hY12, hY21, hYτ, hW12, hW21, hW0⟩ :=
    diagBlocks_relations h02 h03 h12 h13 h20 h21 h30 h31 hK
  obtain ⟨hYne, hWne⟩ := diagBlocks_ne_zero hSdet h02 h03 h20 h21
  have hY0 : (!![S 0 0, S 0 1; S 1 0, S 1 1] : Matrix (Fin 2) (Fin 2) F) *
      !![0, 1; 1, 0] = !![0, 1; 1, 0] * !![S 0 0, S 0 1; S 1 0, S 1 1] := by
    simpa using hYτ 0
  obtain ⟨lam, hlam0, hY⟩ :=
    exists_eq_smul_one_of_diagBlocks_relations hYne hY12 hY21 hY0
  obtain ⟨mu, hmu0, hW⟩ :=
    exists_eq_smul_one_of_diagBlocks_relations hWne hW12 hW21 hW0
  refine ⟨eq_one_of_diagBlocks_relations hYne hY12 hY21 hYτ, ?_⟩
  rw [eq_diagonal_of_eq_smul_one hY hW h02 h03 h12 h13 h20 h21 h30 h31]
  exact diagonal_pow_card_sub_one hlam0 hmu0

theorem offDiagBlock_relations {S : Matrix (Fin 4) (Fin 4) F} {ψ : F ≃+* F} {a : F}
    (h00 : S 0 0 = 0) (h01 : S 0 1 = 0) (h10 : S 1 0 = 0) (h11 : S 1 1 = 0)
    (hK : ∀ (B : Matrix (Fin 2) (Fin 2) F), B.det = 1 →
      S * (blkS (unitaryInvolution F 2 b) B).map ψ = blkS (unitaryInvolution F 2 b) B * S) :
    (!![S 0 2, S 0 3; S 1 2, S 1 3] : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1] =
        !![1, 1; 0, 1] * !![S 0 2, S 0 3; S 1 2, S 1 3] ∧
      (!![S 0 2, S 0 3; S 1 2, S 1 3] : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1] =
        !![1, 0; 1, 1] * !![S 0 2, S 0 3; S 1 2, S 1 3] ∧
      (!![S 0 2, S 0 3; S 1 2, S 1 3] : Matrix (Fin 2) (Fin 2) F) *
          !![ψ (unitaryInvolution F 2 b a), 1; 1, 0] =
        !![a, 1; 1, 0] * !![S 0 2, S 0 3; S 1 2, S 1 3] := by
  have mapE12 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).map (unitaryInvolution F 2 b) := by
    rw [map_fin_two]; simp
  have mapE21 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) =
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F).map (unitaryInvolution F 2 b) := by
    rw [map_fin_two]; simp
  have mapA : (!![unitaryInvolution F 2 b a, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) =
      (!![a, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).map (unitaryInvolution F 2 b) := by
    rw [map_fin_two]; simp
  have detB : ∀ τ : F, (!![τ, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    intro τ
    rw [Matrix.det_fin_two]
    simp [CharTwo.neg_eq]
  refine ⟨?_, ?_, ?_⟩
  · simpa [map_fin_two] using
      (offDiagBlocks_mul_of_mul_blkS (σ := unitaryInvolution F 2 b) (ψ := (ψ : F →+* F))
        mapE12 h00 h01 h10 h11
        (hK (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) (by rw [Matrix.det_fin_two]; norm_num)))
  · simpa [map_fin_two] using
      (offDiagBlocks_mul_of_mul_blkS (σ := unitaryInvolution F 2 b) (ψ := (ψ : F →+* F))
        mapE21 h00 h01 h10 h11
        (hK (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) (by rw [Matrix.det_fin_two]; norm_num)))
  · simpa [map_fin_two] using
      (offDiagBlocks_mul_of_mul_blkS (σ := unitaryInvolution F 2 b) (ψ := (ψ : F →+* F))
        mapA h00 h01 h10 h11 (hK (!![a, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) (detB a)))

theorem false_of_offDiag_fix {ω : rootsOfUnity 3 F} (hbe : Even b)
    (hω : ω ≠ 1) {ψ : F ≃+* F} {S : Matrix (Fin 4) (Fin 4) F}
    (hSdet : S.det ≠ 0) (hψa : ψ ((ω : Fˣ) : F) = (((ω : Fˣ) : F))⁻¹)
    (hK : ∀ (B : Matrix (Fin 2) (Fin 2) F), B.det = 1 →
      S * (blkS (unitaryInvolution F 2 b) B).map ψ = blkS (unitaryInvolution F 2 b) B * S)
    (hT : S * (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F).map ψ =
      (((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) * S) :
    False := by
  obtain ⟨h00, h01, h10, h11⟩ := upperBlocks_eq_zero_of_commute_torusD_inv hω hψa hT
  have hXne := ne_zero_of_upperRight_block hSdet h00 h01
  obtain ⟨hX12, hX21, hXa⟩ := offDiagBlock_relations (a := ((ω : Fˣ) : F)) h00 h01 h10 h11 hK
  set a : F := ((ω : Fˣ) : F) with ha
  obtain ⟨-, -, -, hainv⟩ := pow_three_and_ne_of_rootsOfUnity ha hω
  have hψa' : ψ a = a⁻¹ := by rw [ha]; exact hψa
  have hσa : unitaryInvolution F 2 b a = a := by
    rw [ha]
    exact unitaryInvolution_rootsOfUnity (F := F) hbe ω
  have hψσa : ψ (unitaryInvolution F 2 b a) = a :=
    (eq_smul_one_and_eq_of_mul_specialSL hXne hX12 hX21 hXa).2.2
  have hψaa : ψ a = a := by
    have h := hψσa
    rwa [hσa] at h
  exact hainv (by rw [← hψa']; exact hψaa.symm)

theorem eq_one_of_fix_shortSL_torusD (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    (α : MulAut ↥(SU (unitaryInvolution F 2 b) 4)) (hα : ∃ k : ℕ, α ^ 2 ^ k = 1)
    (hK : ∀ x : ↥(SU (unitaryInvolution F 2 b) 4),
      (x : GL (Fin 4) F) ∈ shortSL (unitaryInvolution F 2 b) → α x = x)
    (ht : ∀ x : ↥(SU (unitaryInvolution F 2 b) 4),
      (x : GL (Fin 4) F) = torusD ((ω, ω) : D8Mod 3 F) → α x = x) :
    α = 1 := by
  classical
  obtain ⟨k, hk⟩ := hα
  have hdata : UnitaryFieldData 2 b F :=
    { prime := Nat.prime_two
      one_le := one_le_of_card_eq_two_pow_sq hF
      card := by rw [hF, ← pow_mul, Nat.mul_comm b 2] }
  have hSU := su_eq_gramSU_miyamotoJ4 hdata
  let e : ↥(SU (unitaryInvolution F 2 b) 4) ≃*
      gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F) := MulEquiv.subgroupCongr hSU
  set β : MulAut (gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F)) := MulAut.congr e α with hβ
  obtain ⟨s, hs⟩ := CFSG.LocalAnalysis.EvenBN.U4.exists_eq_conj_mul_fieldAut hdata β
  set ψ : F ≃+* F := CFSG.LocalAnalysis.EvenBN.U4.miyamotoFieldFactor hdata β with hψ
  have hform : ∀ g : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F),
      ((β g : gramSU hdata (CFSG.LocalAnalysis.miyamotoJ4 F)) : GL (Fin 4) F) =
        s * glAut ψ (g : GL (Fin 4) F) * s⁻¹ := fun g => coe_eq_mul_glAut_mul_inv hs g
  have hcongr : ∀ x : ↥(SU (unitaryInvolution F 2 b) 4), β (e x) = e (α x) := by
    intro x
    simp [hβ, e, MulAut.congr]
  obtain ⟨hfixK, hfixT⟩ := fixed_relations hform hcongr hbe hF hK ht
  have hSdet : (((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp (Matrix.isUnits_det_units (s : GL (Fin 4) F))
  rcases fieldAut_apply_eq_or_eq_inv (card_rootsOfUnity_three hbe hF) hω ψ with hψa | hψa
  · obtain ⟨hψ1, hSpow⟩ := eq_one_and_pow_of_fix_blkS hω hSdet hψa hfixK hfixT
    have hβconj : β = MulAut.conj s := by
      rw [hs, hψ1, ← CFSG.LocalAnalysis.EvenBN.U4.miyamotoFieldHom_apply, map_one, mul_one]
    have hspow : s ^ (Nat.card F - 1) = 1 := by
      apply Subtype.ext
      apply Units.ext
      simpa using hSpow
    have hβpow : β ^ (Nat.card F - 1) = 1 := by
      rw [hβconj, (map_pow MulAut.conj s (Nat.card F - 1)).symm, hspow, map_one]
    have hαpow : α ^ (Nat.card F - 1) = 1 := by
      have h : MulAut.congr e (α ^ (Nat.card F - 1)) = 1 := by
        rw [map_pow, show MulAut.congr e α = β from hβ.symm, hβpow]
      exact (MulAut.congr e).injective (by rw [h, map_one])
    exact (pow_eq_one_iff_of_coprime (coprime_two_pow_card_sub_one hF k)).mp ⟨hk, hαpow⟩
  · exact (false_of_offDiag_fix hbe hω hSdet hψa hfixK hfixT).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.AutOdd

end
