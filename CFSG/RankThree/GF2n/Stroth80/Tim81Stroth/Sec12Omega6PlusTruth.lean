module

public import CFSG.RankThree.GF2n.Smith81.Statement
public import CFSG.RankThree.GF2n.Stroth80.Sec12Omega6PlusCfg

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem caseE6_of_secondCfgCaseE6Four {X : Type} [Group X] {N B₂ : Subgroup X}
    (h : SecondCfgCaseE6Four N B₂) :
    CFSG.RankThree.GF2n.Smith81.CaseE6
      (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) N (cen N) B₂ 4 := by
  obtain ⟨-, K, iF, iK, hK, φ, hφr, hφk, V₁, V₂, hZV₁, hV₁N, hZV₂, hV₂N, hinf, hsup,
    hact₁, hact₂, hx, hCD⟩ := h
  exact ⟨K, iF, iK, hK, φ, hφr, hφk, V₁, V₂, hZV₁, hV₁N, hZV₂, hV₂N, hinf, hsup,
    hact₁, hact₂, hx, hCD⟩

end CFSG.RankThree.GF2n.Stroth80
