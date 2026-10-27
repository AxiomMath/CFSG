module

public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannBasic
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannReduced
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannCComp
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannBlockTypes
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannOmegaZ
public import CFSG.Milestones.ASVolI.C1

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open scoped Pointwise

section C124



variable {X : Type} [Group X] [Finite X]

theorem concl315_of_c124
    (hF : generalizedFitting X = CFSG.pCore 2 X)
    {A S : Subgroup X} (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2))
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))) {m : ℕ}
    (halt : CFSG.Quasithin.IsAltQuotient (oResidual 2 X)
      (CFSG.Quasithin.oTwoZIn (oResidual 2 X)) m)
    (hm : m = 5 ∨ m = 7 ∨ (m = 6 ∧ S ≤ oResidual 2 X ⊔ CFSG.pCore 2 X))
    (hX : Nontrivial X) (hnorm : (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X).Normal) :
    Concl315 X S := by
  have hOS : CFSG.pCore 2 X ≤ S := Push153.pCore_le_of_mem_maxInvariant hS
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2.1
  by_cases hWL : ⁅W315 X, oResidual 2 X⁆ = ⊥
  · exact concl315_of_commutator_eq_bot hF hS hX hWL hnorm
  obtain ⟨T, hT, hST⟩ := exists_sylow_le hS2
  have hHyp : CFSG.ASVolI.ChC.HypC_1_14 (⊤ : Subgroup X) (W315 X) T :=
    ⟨charTwo_top_of_hF hF, isTwoReducedIn_W315 hq hWL, hT⟩
  have hm' : (m = 5 ∨ m = 7) ∨
      (m = 6 ∧ CFSG.Quasithin.autOn S (W315 X) ≤ CFSG.Quasithin.autOn (oResidual 2 X) (W315 X)) ∨
      (m = 6 ∧ Nat.card ↥(CFSG.Quasithin.autOn S (W315 X)) = 2) := by
    rcases hm with h | h | ⟨h6, hle⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl ⟨h6, autOn_le_of_le_sup hle⟩)
  rcases CFSG.ASVolI.as_C_1_24 X ⊤ (W315 X) T (oResidual 2 X) S hHyp
      (top_eq_mul_of_sylow hT) (oResidual_mem_cComp hq) (charTwo_oResidual hF) hWL
      (pCoreOf_top_le hOS) hST m halt hm' with h | h | ⟨hb, h⟩ | ⟨hb, h⟩ | ⟨hb, h⟩
  · obtain ⟨D, hD1, hDB, hDc, hDn⟩ := h
    left
    refine ⟨D, hD1, hDB.trans (CFSG.Quasithin.C1GN.baum_le S),
      CFSG.Quasithin.C1GN.characteristic_subgroupOf_trans (CFSG.Quasithin.C1GN.baum_le S) hDB
        (CFSG.Quasithin.C1GN.characteristic_baum S) hDc, ?_⟩
    rw [← Subgroup.normalizer_eq_top_iff]
    exact top_le_iff.mp hDn
  · exact Or.inr (isScriptLBlock_of_isChiBlock2 h)
  · exact Or.inr (isScriptLBlock_of_isExcA7Block hb h)
  · exact Or.inr (isScriptLBlock_of_isAltBlockType6 hb h)
  · exact Or.inr (isScriptLBlock_of_isHatA6Block hb h)

end C124

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
