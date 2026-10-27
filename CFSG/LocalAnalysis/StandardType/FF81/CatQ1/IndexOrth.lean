module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.FieldPOmegaOdd
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.FieldPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.FieldPOmegaMinus
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open TauCeti CFSG.RankThree.PartTwo.Census

theorem outerThreeBig_B_odd :
    OuterThreeBigAt (fun i => ∃ r q, i = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r) := by
  rintro K _ _ d ⟨r, q, hd, hp, hr⟩ ⟨e⟩
  obtain ⟨i, hv⟩ := d
  obtain rfl : i = .B r q := hd
  exact outerThreeBig_of_modelPOmegaOdd (statedClassicalModel_typeB_odd r q hv hp hr e)

theorem outerThreeBig_D : OuterThreeBigAt (fun i => ∃ r q, i = .D r q ∧ 5 ≤ r) := by
  rintro K _ _ d ⟨r, q, hd, hr⟩ ⟨e⟩
  obtain ⟨i, hv⟩ := d
  obtain rfl : i = .D r q := hd
  exact outerThreeBig_of_modelPOmegaPlus hr (statedClassicalModel_typeD r q hv e)

theorem outerThreeBig_twistedD : OuterThreeBigAt (fun i => ∃ r q, i = .twistedD r q) := by
  rintro K _ _ d ⟨r, q, hd⟩ ⟨e⟩
  obtain ⟨i, hv⟩ := d
  obtain rfl : i = .twistedD r q := hd
  exact outerThreeBig_of_modelPOmegaMinus (statedClassicalModel_typeTwistedD r q hv e)

end CFSG.StandardType.FF81.CatQ1
