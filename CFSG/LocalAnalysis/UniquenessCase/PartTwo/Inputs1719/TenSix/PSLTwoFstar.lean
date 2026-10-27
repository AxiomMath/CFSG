module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.L2Case
import CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3
import CFSG.GroupTheory.TwoElementSquare

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem aParam_le_of_fstar_psl2
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {F : Type} [Field F] [Finite F] (hF2 : (2 : F) ≠ 0)
    (h3 : 3 < Nat.card F) (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hFs : Fstar Y = L)
    (e : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    (9 < Nat.card F → E3.aParam Y ≤ 1) ∧ E3.aParam Y ≤ 2 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hchar, n, hp, hcardFintype⟩ := FiniteField.card' F
  have hcard : Nat.card F = p ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardFintype]
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := hchar
    exact hF2 (CharP.cast_eq_zero F 2)
  have h4 : 4 ≤ Nat.card F := by omega
  have h4p : 4 ≤ p ^ (n : ℕ) := by rw [← hcard]; exact h4
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have : IsSimpleGroup ↥L := e.isSimpleGroup
  have hnab : ∃ a b : ↥L, a * b ≠ b * a :=
    CFSG.Walter.exists_mul_ne_mul_of_mulEquiv_psl2 h4 e
  have hLq : IsQuasisimple ↥L := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  have hO2 : O2Trivial L := by
    intro P hPL hPn hP2
    have : (P.subgroupOf L).Normal := hPn
    have hP2' : IsPGroup 2 (P.subgroupOf L) :=
      hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
    have hbot : P.subgroupOf L = ⊥ :=
      CFSG.eq_bot_of_normal_isPGroup_of_isSimpleGroup hnab hP2'
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hPL hx⟩ : ↥L) ∈ P.subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hx')
  have hZ : Subgroup.center ↥L = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
      (CFSG.GorensteinWalter.psl2_center_eq_bot F)
  let eX : (↥L ⧸ Subgroup.center ↥L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)
  have hM : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 p (n : ℕ) :=
    CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3.lieModel_psl2_of_equiv hp n.pos h4p hcard eX
  have hmain := w4Lem10_6_psl2 hW hLY hLn hFs hLq hO2 hp2 hM
  refine ⟨fun h9 => ?_, hmain.2⟩
  have h9' : 9 < p ^ (n : ℕ) := by rw [← hcard]; exact h9
  exact le_of_eq (hmain.1 h9')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
