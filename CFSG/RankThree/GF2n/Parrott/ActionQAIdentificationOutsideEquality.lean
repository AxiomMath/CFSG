module

public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentificationRigid
public import CFSG.RankThree.GF2n.Parrott.Section2CJ
public import CFSG.RankThree.GF2n.Parrott.E27LineCount

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LinearAlgebra.F2Cube (fixedCount)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]

theorem generatorConjugacy_of_not_equalityBranch (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) :
    GeneratorConjugacy (z := z) h D := by
  obtain ⟨σ₂, hσ₂, hq₂, hc₂⟩ := exists_commuting_order_three_lift_sigma2 (z := z) D h
  have hE27 := e27LineCountData_of_not_equalityBranch D h hIII hσ₂ hq₂ hc₂
  have hx := fixDimV_sigma1Nine_mul_sigma2_eq_zero_of_not_equalityBranch D h hIII hσ₂ hq₂ hc₂
    hE27
  have hy := fixDimV_sigma1Nine_mul_sigma2_inv_eq_four_of_not_equalityBranch D h hIII hσ₂ hq₂
    hc₂ hE27
  have c1 : fixedCount ((actionQA45 (z := z) h D spinE27a : GL8) : Mat8) = 4 := by
    rw [← qH_sigma1Nine_eq_spinE27a D, fixedCount_actionQA45_qH, fixDimV_sigma1Nine]
    norm_num
  have c2 : fixedCount ((actionQA45 (z := z) h D (spinE27a * spinE27b) : GL8) : Mat8) = 1 := by
    have h' := fixedCount_actionQA45_qH D h (sigma1Nine (z := z) D * σ₂)
    rw [map_mul, qH_sigma1Nine_eq_spinE27a, qH_eq_spinE27b D hq₂, hx] at h'
    exact h'
  have c3 : fixedCount ((actionQA45 (z := z) h D (spinE27a * spinE27b⁻¹) : GL8) : Mat8) =
      16 := by
    have h' := fixedCount_actionQA45_qH D h (sigma1Nine (z := z) D * σ₂⁻¹)
    rw [map_mul, map_inv, qH_sigma1Nine_eq_spinE27a, qH_eq_spinE27b D hq₂, hy] at h'
    rw [h']
    norm_num
  obtain ⟨P₀, hP₀⟩ := exists_conj_on_spinE27 (actionQA45 (z := z) h D) rhoA
    (actionQA45_spinE27_eq_zero_of_fixed D h hIII hσ₂ hq₂ hc₂) rhoA_eq_zero_of_fixed
    (by rw [c1, fixedCount_rhoA_spinE27a]) (by rw [c2, fixedCount_rhoA_spinE27ab])
    (by rw [c3, fixedCount_rhoA_spinE27abinv])
  exact generatorConjugacy_of_agree_on_spinE27 h D P₀ hP₀

end CFSG.RankThree.GF2n.Parrott
