module

public import CFSG.RankThree.PartOne.LSTD.ClsN
public import CFSG.RankThree.PartOne.KFOUT3.L12Ker
public import CFSG.RankThree.PartOne.LSTD.HyperEq

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)

variable {f : ℕ} {K : Type} [Field K]

theorem suBlock12_eq_emb3 (hU : UnitaryFieldData 2 f K) : KFOUT3.suBlock12 hU = emb3 hU := by
  apply MonoidHom.ext
  intro A
  apply Subtype.ext
  apply Units.ext
  rw [KFOUT3.coe_suBlock12]
  show _ = blockMat 5 0 ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  ext a b
  rw [blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp [KFOUT3.blkB]

theorem range_suBlock12_map (hU : UnitaryFieldData 2 f K) :
    (KFOUT3.suBlock12 hU).range.map (projU K f) = (theta3 hU).range := by
  rw [suBlock12_eq_emb3, theta3, MonoidHom.range_comp]

theorem card_range_theta3 (hU : UnitaryFieldData 2 f K) :
    Nat.card ↥(theta3 hU).range = Nat.card ↥(unitarySU 2 f K 3) :=
  Nat.card_congr (MonoidHom.ofInjective (theta3_injective hU)).toEquiv.symm

theorem projU_tSU_eq_bB (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    {w : Fin 5 → Kˣ} (hw : w ∈ torusVec 5 5 K) (hA : A5 w) :
    ∃ (t : Kˣ) (ht : t ^ 5 = 1), t ≠ 1 ∧
      projU K f (tSU hU h5 w hw) = projU K f (KFOUT3.bB hU h5 ht) := by
  obtain ⟨h01, h12, h30, h40, h34⟩ := hA
  have hw5 : ∀ i, w i ^ 5 = 1 := hw.1
  have hprod : w 0 * w 1 * w 2 * w 3 * w 4 = 1 := by
    have := hw.2
    rwa [Fin.prod_univ_five] at this
  refine ⟨w 0 * (w 3)⁻¹, ?_, ?_, ?_⟩
  · rw [mul_pow, inv_pow, hw5, hw5, inv_one, one_mul]
  · intro h
    apply h30
    have := mul_inv_eq_one.mp h
    exact this.symm
  · have ht5 : (w 0 * (w 3)⁻¹) ^ 5 = 1 := by
      rw [mul_pow, inv_pow, hw5, hw5, inv_one, one_mul]
    have hw4 : w 4 = w 0 ^ 2 * (w 3)⁻¹ := by
      have h02 : w 0 = w 2 := h01.trans h12
      have h1 : w 0 ^ 3 * w 3 * w 4 = 1 := by
        have h := hprod
        rw [← h02, ← h01] at h
        calc w 0 ^ 3 * w 3 * w 4 = w 0 * w 0 * w 0 * w 3 * w 4 := by
              simp only [pow_succ, pow_zero, one_mul]
          _ = 1 := h
      have h2 : w 4 = (w 0 ^ 3 * w 3)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 : (w 0 ^ 3)⁻¹ = w 0 ^ 2 := by
        symm
        apply eq_inv_of_mul_eq_one_right
        rw [← pow_add]
        exact hw5 0
      rw [h2, mul_inv, h3]
    have hz3 : (fun _ : Fin 5 => w 3) ∈ torusVec 5 5 K :=
      ⟨fun _ => hw5 3, by simp [Finset.prod_const, hw5 3]⟩
    apply projU_eq_iff.mpr
    refine ⟨tSU hU h5 (fun _ => w 3) hz3, const_mem_scalarsU hU h5 hz3, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_tSU, coe_tSU]
    show diagU w = diagU (KFOUT3.dvecB (w 0 * (w 3)⁻¹)) * diagU (fun _ => w 3)
    rw [diagU_mul]
    congr 1
    funext i
    fin_cases i
    · simp [KFOUT3.dvecB]
    · simp [KFOUT3.dvecB, h01]
    · simp [KFOUT3.dvecB, h12, h01]
    · simp [KFOUT3.dvecB]
    · simp [KFOUT3.dvecB, hw4, mul_pow]
      group

theorem le_inSubgroup_perfectResidual' {H : Type*} [Group H] {P Y : Subgroup H} (hPY : P ≤ Y)
    (hP : Group.IsPerfect ↥P) : P ≤ inSubgroup perfectResidual Y :=
  CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf P Y hP hPY

theorem eq_range_of_bB [Finite K] (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ}
    (ht : t ^ 5 = 1) (h1 : t ≠ 1) (X : Subgroup (StatedProj (unitarySU 2 f K 5)))
    (hX : Group.IsPerfect ↥X)
    (hXc : X ≤ Subgroup.centralizer
      ({projU K f (KFOUT3.bB hU h5 ht)} : Set (StatedProj (unitarySU 2 f K 5))))
    (hXcard : Nat.card ↥X = Nat.card ↥(unitarySU 2 f K 3)) : X = (theta3 hU).range := by
  have : CharP K 2 := hU.charP
  have hle := le_inSubgroup_perfectResidual' hXc hX
  rw [KFOUT3.perfectResidual_centralizer_proj hU h5 ht h1, range_suBlock12_map] at hle
  have : Finite ↥(theta3 hU).range := by
    have : Finite ↥(unitarySU 2 f K 3) := inferInstance
    exact Finite.of_injective _ (MonoidHom.ofInjective (theta3_injective hU)).symm.injective
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_range_theta3, hXcard])

theorem projU_bB_mem_Jfun (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ}
    (ht : t ^ 5 = 1) : projU K f (KFOUT3.bB hU h5 ht) ∈ Jfun hU 3 4 := by
  have hu : (t⁻¹) ^ 5 = 1 := by rw [inv_pow, ht, inv_one]
  have hvm : torusElt 3 4 t⁻¹ ∈ torusVec 5 5 K := torusElt_mem (by decide) hu
  have hzm : (fun _ : Fin 5 => t) ∈ torusVec 5 5 K :=
    ⟨fun _ => ht, by simp [Finset.prod_const, ht]⟩
  have hx : projU K f (KFOUT3.bB hU h5 ht) =
      projU K f (tSU hU h5 (torusElt 3 4 t⁻¹) hvm) := by
    apply projU_eq_iff.mpr
    refine ⟨tSU hU h5 (fun _ => t) hzm, const_mem_scalarsU hU h5 hzm, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_tSU, coe_tSU, diagU_mul]
    show diagU (KFOUT3.dvecB t) = diagU (torusElt 3 4 t⁻¹ * fun _ => t)
    congr 1
    funext i
    fin_cases i <;> simp [KFOUT3.dvecB, torusElt, pow_two]
  rw [hx, Jfun_of_ne hU (by decide : (3 : Fin 5) ≠ 4)]
  exact ⟨_, lineElt_mem_Bk hU h5 (by decide) hu, rfl⟩

end CFSG.RankThree.PartOne.LSTD
