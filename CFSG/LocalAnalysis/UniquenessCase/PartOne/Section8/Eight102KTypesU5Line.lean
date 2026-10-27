module

public import CFSG.RankThree.PartOne.KF.R6LeviA
public import CFSG.RankThree.PartOne.KF.R56Final
import CFSG.GroupTheory.ConjTransport
import CFSG.RankThree.PartTwo.KFacts.KS222U5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open Subgroup
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.RankThree.PartOne (suQ isCentralPQuot_suQ)
open CFSG.RankThree.PartOne.KFU (bA6 b6 coe_bA6 coe_b6 diagU diagU_injective diagU_one
  diagU_pow dvec5)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem cube_eq_one_of_eq_bA6 {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ)
    {w : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hw : w = bA6 (unitaryInvolution K 2 2) ζ hζ) (hw3 : w ^ 3 = 1) : ζ ^ 3 = 1 := by
  rw [hw] at hw3
  have h2 : (diagU (dvec5 1 ζ) : GL (Fin 5) K) ^ 3 = 1 := by
    have h := congrArg (fun u : ↥(SU (unitaryInvolution K 2 2) 5) =>
      (u : GL (Fin 5) K)) hw3
    simpa only [Subgroup.coe_pow, coe_bA6, Subgroup.coe_one] using h
  have h3 : (dvec5 1 ζ) ^ 3 = 1 := by
    refine diagU_injective ?_
    rw [← diagU_pow, h2, diagU_one]
  simpa [dvec5] using congrFun h3 1

private theorem cube_eq_one_of_eq_b6 {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ)
    {w : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hw : w = b6 (unitaryInvolution K 2 2) ζ hζ) (hw3 : w ^ 3 = 1) : ζ ^ 3 = 1 := by
  rw [hw] at hw3
  have h2 : (diagU (dvec5 ζ ζ) : GL (Fin 5) K) ^ 3 = 1 := by
    have h := congrArg (fun u : ↥(SU (unitaryInvolution K 2 2) 5) =>
      (u : GL (Fin 5) K)) hw3
    simpa only [Subgroup.coe_pow, coe_b6, Subgroup.coe_one] using h
  have h3 : (dvec5 ζ ζ) ^ 3 = 1 := by
    refine diagU_injective ?_
    rw [← diagU_pow, h2, diagU_one]
  simpa [dvec5] using congrFun h3 0

omit [CharP K 2] in
private theorem eq_or_eq_inv_of_cube (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ ζ' : Kˣ}
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) (hζ'3 : ζ' ^ 3 = 1) (hζ'1 : ζ' ≠ 1) :
    ζ' = ζ ∨ ζ' = ζ⁻¹ := by
  have hμ : Nat.card (rootsOfUnity 3 K) = 3 :=
    CFSG.RankThree.PartTwo.Sec21.U4Lines.card_rootsOfUnity_three even_two hK
  have hω : (⟨ζ, (mem_rootsOfUnity 3 ζ).mpr hζ3⟩ : rootsOfUnity 3 K) ≠ 1 :=
    fun h => hζ1 (congrArg Subtype.val h)
  rcases CFSG.RankThree.PartTwo.Sec21.U4Lines.eq_one_or_eq_or_eq_inv hμ hω
      (⟨ζ', (mem_rootsOfUnity 3 ζ').mpr hζ'3⟩ : rootsOfUnity 3 K) with h | h | h
  · exact absurd (congrArg Subtype.val h) hζ'1
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (by simpa using congrArg Subtype.val h)

private theorem bA6_inv {ζ : Kˣ} (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ)
    (hζ' : unitaryInvolution K 2 2 ((ζ⁻¹ : Kˣ) : K) = ζ⁻¹) :
    bA6 (unitaryInvolution K 2 2) ζ⁻¹ hζ' =
      (bA6 (unitaryInvolution K 2 2) ζ hζ)⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_inv, coe_bA6, coe_bA6, ← CFSG.RankThree.PartOne.KFU.diagU_inv]
  congr 1
  funext i
  fin_cases i <;> simp [dvec5]

private theorem b6_inv {ζ : Kˣ} (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ)
    (hζ' : unitaryInvolution K 2 2 ((ζ⁻¹ : Kˣ) : K) = ζ⁻¹) :
    b6 (unitaryInvolution K 2 2) ζ⁻¹ hζ' =
      (b6 (unitaryInvolution K 2 2) ζ hζ)⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_inv, coe_b6, coe_b6, ← CFSG.RankThree.PartOne.KFU.diagU_inv]
  congr 1
  funext i
  fin_cases i <;> simp [dvec5]

private theorem zpowers_suQ_eq_of_eq (hK : Nat.card K = (2 ^ 2) ^ 2)
    {x h A : ↥(SU (unitaryInvolution K 2 2) 5)}
    {y : StatedProj (StatedSU 5 (2 ^ 2) K)}
    (hxy : suQ 5 hK x = y) (hA : h * x * h⁻¹ = A) :
    Subgroup.zpowers (suQ 5 hK A) =
      Subgroup.zpowers (suQ 5 hK h * y * (suQ 5 hK h)⁻¹) := by
  rw [← hA, map_mul, map_mul, map_inv, hxy]

private theorem zpowers_suQ_eq_of_inv (hK : Nat.card K = (2 ^ 2) ^ 2)
    {x h A : ↥(SU (unitaryInvolution K 2 2) 5)}
    {y : StatedProj (StatedSU 5 (2 ^ 2) K)}
    (hxy : suQ 5 hK x = y) (hA : h * x * h⁻¹ = A⁻¹) :
    Subgroup.zpowers (suQ 5 hK A) =
      Subgroup.zpowers (suQ 5 hK h * y * (suQ 5 hK h)⁻¹) := by
  rw [← Subgroup.zpowers_inv]
  congr 1
  rw [← map_inv, ← hA, map_mul, map_mul, map_inv, hxy]

theorem u5_conj_line (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    {Y : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))} (hY : Nat.card Y = 3) :
    ∃ g : StatedProj (StatedSU 5 (2 ^ 2) K),
      Y = (zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ))).map
          (MulAut.conj g).toMonoidHom ∨
        Y = (zpowers (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ))).map
          (MulAut.conj g).toMonoidHom := by
  obtain ⟨y, -, hy1, hy3, hYy⟩ :=
    CFSG.RankThree.PartTwo.Sec21.U5Lines.exists_eq_zpowers_of_card_three hY
  have hq : CFSG.RankThree.PartOne.KFU.IsCentralPQuot 3 (suQ 5 hK) :=
    isCentralPQuot_suQ (K := K) (n := 5) (f := 2) Nat.prime_three (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hK
  obtain ⟨x, hxy, hx3⟩ := hq.exists_lift hy3
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hy1 (by rw [← hxy, map_one])
  obtain ⟨h, ζ', hζ', hζ'1, _, hcase⟩ :=
    CFSG.RankThree.PartTwo.Sec21.U5Lines.exists_conj_eq_bA6_or_b6 hK hx3 hx1
  have hcube : (h * x * h⁻¹) ^ 3 = 1 := by
    have hconj : h * x * h⁻¹ = (MulAut.conj h).toMonoidHom x := by
      simp [MulAut.conj_apply]
    rw [hconj, ← MonoidHom.map_pow, hx3, MonoidHom.map_one]
  have hζ'3 : ζ' ^ 3 = 1 := by
    rcases hcase with hcase | hcase
    · exact cube_eq_one_of_eq_bA6 hζ' hcase hcube
    · exact cube_eq_one_of_eq_b6 hζ' hcase hcube
  rcases hcase with hcase | hcase
  · rcases eq_or_eq_inv_of_cube hK h3 h1 hζ'3 hζ'1 with hζ'eq | hζ'eq
    · subst ζ'
      refine ⟨(suQ 5 hK h)⁻¹, Or.inl ?_⟩
      rw [zpowers_suQ_eq_of_eq hK hxy hcase, hYy,
        ← CFSG.GroupTheory.map_conj_zpowers (suQ 5 hK h) y,
        CFSG.GroupTheory.map_conj_map_conj_inv (suQ 5 hK h) (Subgroup.zpowers y)]
    · subst ζ'
      refine ⟨(suQ 5 hK h)⁻¹, Or.inl ?_⟩
      rw [zpowers_suQ_eq_of_inv hK hxy (by rw [hcase, bA6_inv hζ hζ']), hYy,
        ← CFSG.GroupTheory.map_conj_zpowers (suQ 5 hK h) y,
        CFSG.GroupTheory.map_conj_map_conj_inv (suQ 5 hK h) (Subgroup.zpowers y)]
  · rcases eq_or_eq_inv_of_cube hK h3 h1 hζ'3 hζ'1 with hζ'eq | hζ'eq
    · subst ζ'
      refine ⟨(suQ 5 hK h)⁻¹, Or.inr ?_⟩
      rw [zpowers_suQ_eq_of_eq hK hxy hcase, hYy,
        ← CFSG.GroupTheory.map_conj_zpowers (suQ 5 hK h) y,
        CFSG.GroupTheory.map_conj_map_conj_inv (suQ 5 hK h) (Subgroup.zpowers y)]
    · subst ζ'
      refine ⟨(suQ 5 hK h)⁻¹, Or.inr ?_⟩
      rw [zpowers_suQ_eq_of_inv hK hxy (by rw [hcase, b6_inv hζ hζ']), hYy,
        ← CFSG.GroupTheory.map_conj_zpowers (suQ 5 hK h) y,
        CFSG.GroupTheory.map_conj_map_conj_inv (suQ 5 hK h) (Subgroup.zpowers y)]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
