module

public import CFSG.RankThree.GF2n.Smith81.OrthE1KF7
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseA2
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLieStmts

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem outSolvableList_holds : OutSolvableListStatement := by
  intro X _ _ hX P hP
  haveI : Group.IsPerfect P := ⟨hP⟩
  exact CFSG.RankThree.GF2n.Smith81.Smith23E1.listNoPerfectOut_holds X hX
    (CFSG.RankThree.GF2n.Smith81.Smith23E1.listGroup_isSimpleGroup hX) P
    Subgroup.commutator_eq_self

end Certs

end CFSG.RankThree.GF2n.Stroth80
