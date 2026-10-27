module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.FieldPSp
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open TauCeti

theorem outerThreeBig_B_two : OuterThreeBigAt (fun i => ∃ q, i = .B 2 q) := by
  rintro K _ _ d ⟨q, hd⟩ ⟨e⟩
  obtain ⟨i, hv⟩ := d
  obtain rfl : i = .B 2 q := hd
  exact outerThreeBig_of_modelPSp
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)

theorem outerThreeBig_B_even :
    OuterThreeBigAt (fun i => ∃ r q, i = .B r q ∧ q.p = 2 ∧ 3 ≤ r) := by
  rintro K _ _ d ⟨r, q, hd, hp, hr⟩ ⟨e⟩
  obtain ⟨i, hv⟩ := d
  obtain rfl : i = .B r q := hd
  exact outerThreeBig_of_modelPSp
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr e)

theorem outerThreeBig_C : OuterThreeBigAt (fun i => ∃ r q, i = .C r q) := by
  rintro K _ _ d ⟨r, q, hd⟩ ⟨e⟩
  obtain ⟨i, hv⟩ := d
  obtain rfl : i = .C r q := hd
  exact outerThreeBig_of_modelPSp
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e)

end CFSG.StandardType.FF81.CatQ1
