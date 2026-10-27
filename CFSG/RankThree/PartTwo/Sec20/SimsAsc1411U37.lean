module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Tools
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U37Group
import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

theorem noSmall1411_of_U3_7 (h : Hyp1411 X L S)
    (hD : StatedClassicalModel ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) .PSU 3 7 1) :
    NoSmall1411 X L S := by
  have hsimp := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 7 1 hD).2
  obtain ⟨⟨hp, hf1, -⟩, K, _, _, hK, ⟨eD⟩⟩ := hD
  have hu : UnitaryFieldData 7 1 K := ⟨hp, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  set ε := eD.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).symm with hε
  have hZ : Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥ := by
    have e := Subgroup.map_center_eq ε
    rw [center_unitaryPSU_seven hu] at e
    exact (Subgroup.map_eq_bot_iff_of_injective _ ε.injective).mp e
  refine noSmall1411_of_forall_word1411 h hsimp hZ (q := 43) (k := 1) (by norm_num)
    (by norm_num) le_rfl (fun e he1 he8 => by interval_cases e <;> norm_num) fun α hα => ?_
  have hα' : orderOf (MulAut.congr ε α) = 2 := by rw [MulEquiv.orderOf_eq]; exact hα
  obtain ⟨y₁, y₂, y₃, hy⟩ := exists_word1411_U3_7 hu _ hα'
  refine ⟨ε.symm y₁, ε.symm y₂, ε.symm y₃, ?_⟩
  have e1 := word1411_congr ε α (ε.symm y₁) (ε.symm y₂) (ε.symm y₃)
  simp only [MulEquiv.apply_symm_apply] at e1
  rw [pow_one, ← MulEquiv.orderOf_eq ε, ← e1]
  exact hy

theorem statedClassicalModel_of_mulEquiv_projSU3_seven {G : Type} [Group G] [Fact (Nat.Prime 7)]
    (e : G ≃* CFSG.Assembly.RankThreeEven.projSU 3 7 1) : StatedClassicalModel G .PSU 3 7 1 :=
  CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU ⟨by norm_num, le_rfl, le_rfl, by decide⟩ e

theorem statedScalars_subgroupOf_su3_seven_eq_bot [Fact (Nat.Prime 7)] :
    (CFSG.Open.StatedScalars (Fin 3) (GaloisField 7 (2 * 1))).subgroupOf
      (CFSG.Open.StatedSU 3 (7 ^ 1) (GaloisField 7 (2 * 1))) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨x, hx⟩ hxs
  rw [mem_subgroupOf] at hxs
  obtain ⟨c, hc⟩ := hxs
  rw [Subgroup.mem_bot, Subtype.ext_iff, Subgroup.coe_one]
  change x = 1
  have hK : Nat.card (GaloisField 7 (2 * 1)) = (7 ^ 1) ^ 2 := by
    rw [GaloisField.card 7 (2 * 1) (by norm_num)]
    norm_num
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈
      CFSG.Open.StatedSU 3 (7 ^ 1) (GaloisField 7 (2 * 1)) := by
    rw [hc]
    exact hx
  obtain ⟨h3, hq⟩ := (CFSG.LinearGroups.scalar_mem_statedSU_iff (by norm_num) hK (by norm_num)
    c).mp hmem
  have hc1 : c = 1 := by
    have h8 : c ^ 8 = 1 := hq
    have h9 : c ^ 9 = 1 := by rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, h3, one_pow]
    have e : c = c ^ 9 * (c ^ 8)⁻¹ := by group
    rw [e, h9, h8, inv_one, one_mul]
  have hx1 : x = Matrix.GeneralLinearGroup.scalar (Fin 3) c := hc.symm
  rw [hx1, hc1, map_one]

theorem su3_seven_eq_statedSU [Fact (Nat.Prime 7)] :
    Res6.su3 7 1 = CFSG.Open.StatedSU 3 (7 ^ 1) (GaloisField 7 (2 * 1)) := by
  rw [CFSG.PGLModel.statedSU_eq_closure_det]
  rfl

theorem statedClassicalModel_of_mulEquiv_su3_seven {G : Type} [Group G] [Fact (Nat.Prime 7)]
    (e : G ≃* Res6.su3 7 1) : StatedClassicalModel G .PSU 3 7 1 := by
  refine ⟨⟨by norm_num, le_rfl, le_rfl, by decide⟩, GaloisField 7 (2 * 1), inferInstance,
    inferInstance, ?_, ⟨?_⟩⟩
  · rw [GaloisField.card 7 (2 * 1) (by norm_num)]
    norm_num
  · exact e.trans ((MulEquiv.subgroupCongr su3_seven_eq_statedSU).trans
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
        statedScalars_subgroupOf_su3_seven_eq_bot.symm)))

theorem statedClassicalModel_of_U3_7 {G : Type} [Group G] [Fact (Nat.Prime 7)]
    (hL : Nonempty (G ≃* Res6.su3 7 1) ∨
      Nonempty (G ≃* CFSG.Assembly.RankThreeEven.projSU 3 7 1)) :
    StatedClassicalModel G .PSU 3 7 1 := by
  rcases hL with hL | hL
  · exact statedClassicalModel_of_mulEquiv_su3_seven hL.some
  · exact statedClassicalModel_of_mulEquiv_projSU3_seven hL.some

theorem asc82Item1411_U3_7 (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    [Fact (Nat.Prime 7)] (h : Hyp1411 X L S)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSU 3 7 1))
    (hS : IsCyclic ↥(S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal :=
  asc82Item1411_of_noSmall h (relIndex_pCore_le_two_of_isCyclic h hS)
    (noSmall1411_of_U3_7 h (statedClassicalModel_of_U3_7 (Or.inr hL)))

theorem asc82Item1411_U3_7_pRank (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    [Fact (Nat.Prime 7)] (h : Hyp1411 X L S)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃* Res6.su3 7 1) ∨
      Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
        CFSG.Assembly.RankThreeEven.projSU 3 7 1))
    (hS : CFSG.pRank 2 ↥(S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≤ 1) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal :=
  asc82Item1411_of_noSmall h (relIndex_pCore_le_two_of_pRank_le_one h hS)
    (noSmall1411_of_U3_7 h (statedClassicalModel_of_U3_7 hL))

end CFSG.RankThree.PartTwo.Sec20
