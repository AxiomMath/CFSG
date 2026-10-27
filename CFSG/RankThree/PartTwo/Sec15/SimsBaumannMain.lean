module

public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannAlt
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannA6Quasi
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannA6Split
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannL2Dich
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannKGroup
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannL2Sylow
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannL2Triv
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofBaumann

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

section C124

theorem item315For_typeA6Z3
    : Item315For TypeA6Z3 := by
  intro X _ _ hF hT A hA hAmax S hS
  by_cases hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))
  · have hle := le_sup_of_isTripleCover hA hAmax hS hq hT
    refine concl315_of_c124 hF hS hq (isAltQuotient_of_isTripleCover hT)
      (Or.inr (Or.inr ⟨rfl, hle⟩)) (nontrivial_of_isQuasisimple hq) ?_
    have hL : (oResidual 2 X).Normal := Stage1.Thm6.Prod.oResidual_normal 2 X
    rw [sup_assoc, sup_eq_right.mpr hle]
    exact Subgroup.sup_normal _ _
  · have hSQ := le_pCore_of_isTripleCover_not_quasisimple hA hAmax hS hT hq
    have hOS := Push153.pCore_le_of_mem_maxInvariant hS
    have : Nontrivial X := Push153.nontrivial_of_type315 (Or.inr (Or.inl hT))
    have hSeq : S = CFSG.pCore 2 X := le_antisymm hSQ hOS
    left
    refine ⟨CFSG.pCore 2 X, Push153.pCore_ne_bot_of_nontrivial hF, hOS, ?_, CFSG.pCore_normal⟩
    rw [← hSeq, Subgroup.subgroupOf_self]
    infer_instance

theorem concl315_of_typeL2_big
    {X : Type} [Group X] [Finite X]
    (hF : generalizedFitting X = CFSG.pCore 2 X) {A S : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2)) {n : ℕ} (hn : 4 ≤ n) (hev : Even n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) : Concl315 X S := by
  rcases sylow_or_pCore_of_typeL2 (by omega) e hS with hsyl | htriv
  · exact concl315_of_typeL2_sylow hF hS (by omega) e hsyl (isKGroup_of_typeL2 (by omega) e)
      (sup_normal_of_typeL2 (by omega) e S)
  · exact concl315_of_typeL2_trivial hF hA hAmax hS hn hev e htriv

theorem item315For_typeL2Even
    : Item315For TypeL2Even := by
  intro X _ _ hF htype A hA hAmax S hS
  obtain ⟨n, hn1, hev, ⟨e⟩⟩ := htype
  rcases (show n = 2 ∨ 4 ≤ n by obtain ⟨k, hk⟩ := hev; omega) with rfl | h4
  · exact concl315_of_typeL2_two hF hS e
  · exact concl315_of_typeL2_big hF hA hAmax hS h4 hev e

theorem _root_.CFSG.RankThree.PartTwo.Sec15.item3_15_holds
    : Item3_15 :=
  item3_15_of_cases item315For_typeL2Even item315For_typeA6Z3 item315For_typeA7

end C124

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
