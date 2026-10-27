module

public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannC124
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannQuot
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannIndexTwo

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

section C124



theorem item315For_typeA7
    : Item315For TypeA7 := by
  intro X _ _ hF htype A _ _ S hS
  obtain ⟨e⟩ := htype
  have hq := isQuasisimple_of_equiv_alt (by norm_num) e
  exact concl315_of_c124 hF hS hq (isAltQuotient_of_equiv_alt (by norm_num) e)
    (Or.inr (Or.inl rfl)) (nontrivial_of_isQuasisimple hq) (sup_normal_of_equiv_alt (Or.inr rfl) e S)

theorem concl315_of_typeL2_two
    {X : Type} [Group X] [Finite X]
    (hF : generalizedFitting X = CFSG.pCore 2 X) {A S : Subgroup X}
    (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2))
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 2)) : Concl315 X S := by
  obtain ⟨e5⟩ := nonempty_projSL_four_equiv_alt5
  have e' := e.trans e5
  have hq := isQuasisimple_of_equiv_alt (by norm_num) e'
  exact concl315_of_c124 hF hS hq (isAltQuotient_of_equiv_alt (by norm_num) e')
    (Or.inl rfl) (nontrivial_of_isQuasisimple hq) (sup_normal_of_equiv_alt (Or.inl rfl) e' S)

end C124

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
