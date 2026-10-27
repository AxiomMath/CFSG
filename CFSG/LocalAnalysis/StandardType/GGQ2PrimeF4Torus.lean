module

public import CFSG.Fischer.Unitary
public import CFSG.RankThree.PartOne.Q1327C.BU5Diag
import all CFSG.Fischer.F4

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Fischer
open CFSG.RankThree.PartOne.KFU (torusSU diagU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.ClassicalGroups.UnitaryFlag (gramForm gramForm_apply gramForm_isometry_iff)

private theorem f4_unitaryFieldData : UnitaryFieldData 2 1 F4 :=
  ⟨Nat.prime_two, le_rfl, by rw [Nat.card_eq_fintype_card, F4.card]; norm_num⟩

private theorem f4_bar_eq (c : F4) : f4_unitaryFieldData.bar c = c ^ 2 := by
  rw [UnitaryFieldData.bar_apply]
  norm_num

private theorem herm_eq_gramForm_one (x y : W) :
    herm x y = gramForm f4_unitaryFieldData (1 : Matrix (Fin 6) (Fin 6) F4) y x := by
  rw [herm_eq, gramForm_apply, Matrix.one_mulVec]
  exact Finset.sum_congr rfl fun i _ => by dsimp only; rw [f4_bar_eq, mul_comm]

private theorem mem_GU0_iff_mem_primeFormUnitary (g : GL (Fin 6) F4) :
    g ∈ GU0 ↔ g ∈ primeFormUnitary f4_unitaryFieldData (idGram F4 6) := by
  rw [mem_primeFormUnitary, show idGram F4 6 = 1 from Units.val_one, ← gramForm_isometry_iff]
  constructor
  · intro hg x y
    have h := hg y x
    rwa [herm_eq_gramForm_one, herm_eq_gramForm_one] at h
  · intro hg x y
    rw [herm_eq_gramForm_one, herm_eq_gramForm_one]
    exact hg y x

private theorem f4_isPrimitiveRoot_three : IsPrimitiveRoot F4.ω 3 := by
  refine IsPrimitiveRoot.mk_of_lt F4.ω (by norm_num) (by decide) ?_
  intro l hl0 hl3
  interval_cases l <;> decide

theorem exists_conj_le_torusSU {E : Subgroup (GL (Fin 6) F4)} (hE : E ≤ SU0)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h3 : ∀ a ∈ E, a ^ 3 = 1) :
    ∃ y ∈ GU0, E.map (MulAut.conj y⁻¹).toMonoidHom ≤ torusSU 3 6 F4 := by
  have hEU : ∀ a ∈ E, a ∈ primeFormUnitary f4_unitaryFieldData (idGram F4 6) := fun a ha =>
    (mem_GU0_iff_mem_primeFormUnitary a).mp (SU0_le_GU0 (hE ha))
  let G : Subgroup (primeFormUnitary f4_unitaryFieldData (idGram F4 6)) :=
    E.subgroupOf (primeFormUnitary f4_unitaryFieldData (idGram F4 6))
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := fun x hx y hy =>
    Subtype.ext (hcomm _ hx _ hy)
  have hGpow : ∀ x ∈ G, x ^ 3 = 1 := fun x hx => Subtype.ext (h3 _ hx)
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m
    f4_unitaryFieldData f4_isPrimitiveRoot_three (by norm_num) G hGcomm hGpow
  refine ⟨(P : GL (Fin 6) F4), (mem_GU0_iff_mem_primeFormUnitary _).mpr P.2, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨d, hd⟩ := CFSG.RankThree.PartOne.KFU.exists_diagU_of_isDiag (hP ⟨a, hEU a ha⟩ ha)
  have hb : (MulAut.conj (P : GL (Fin 6) F4)⁻¹).toMonoidHom a = diagU d := by
    rw [hd]
    simp
  have hb3 : ((MulAut.conj (P : GL (Fin 6) F4)⁻¹).toMonoidHom a) ^ 3 = 1 := by
    rw [← map_pow, h3 a ha, map_one]
  have hbdet : Matrix.GeneralLinearGroup.det
      ((MulAut.conj (P : GL (Fin 6) F4)⁻¹).toMonoidHom a) = 1 := by
    have hdet_a : Matrix.GeneralLinearGroup.det a = 1 := (mem_SU0.mp (hE ha)).1
    simp [hdet_a]
  rw [hb] at hb3 hbdet ⊢
  refine CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mpr ⟨d, fun i => ?_, ?_, rfl⟩
  · rw [CFSG.RankThree.PartOne.KFU.diagU_pow] at hb3
    exact congrFun (CFSG.RankThree.PartOne.KFU.diagU_injective
      (hb3.trans CFSG.RankThree.PartOne.KFU.diagU_one.symm)) i
  · have h1 := congrArg Units.val hbdet
    rw [Matrix.GeneralLinearGroup.val_det_apply, CFSG.RankThree.PartOne.KFU.det_diagU] at h1
    exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact h1)

end CFSG.GGQ2Prime
