module

public import CFSG.RankThree.PartOne.N1322.Final
public import CFSG.RankThree.PartOne.N1322.CaseSL3
public import CFSG.RankThree.PartOne.N1322.CaseA5
public import CFSG.RankThree.PartOne.N1322.Case6
public import CFSG.RankThree.PartOne.N1322.CaseOmega
public import CFSG.RankThree.PartOne.N1322.CaseA6
public import CFSG.RankThree.PartOne.N1322.CaseHess

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.RepresentationTheory
open CFSG.RankThree.SubgroupLists (omegaGL)

theorem primitive_residual (hBM : ExtBloomMitchell) (hΩ : KF1322OmegaList)
    (hN : KF1322ThreeA6Norm) : PrimitiveResidual := by
  intro p _ d h
  have hp2 : p ≠ 2 := by have := h.p5; omega
  obtain ⟨H, hHX, hnorm, hirrH, hcases⟩ := hBM p hp2 h.irr
  rcases hcases with h1 | ⟨M, hM, hdet, h2⟩ | ⟨⟨e⟩, -, hdec, hinter⟩ | ⟨⟨e⟩, -⟩ |
      ⟨hperf, hcard, ⟨e⟩, -⟩ | ⟨hcyc, -, -⟩ | ⟨hcard, hext, -⟩ | ⟨hHG, hmono⟩
  · exact (case1_false h hHX h1).elim
  · exact (case2_false hΩ h hHX hnorm hirrH M hM hdet h2).elim
  · exact (case3_false h hHX e hdec hinter).elim
  · exact (case4_false h hHX hnorm hirrH e).elim
  · exact (case5_false hN h hHX hnorm hirrH hperf hcard e).elim
  · exact (case6_false h hnorm hirrH hcyc).elim
  · exact (case7_false h hnorm hirrH hcard hext).elim
  · exact hmono

theorem node1322_of_kfacts (hBM : ExtBloomMitchell)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hPairJ : NF7J.PairMember) (hOdd : KF1322Odd) (hKty : KF1322Kty) (hG2 : KF1322G2)
    (hNF7U : NF7H.KF1322NF7U) (hΩ : KF1322OmegaList) (hN : KF1322ThreeA6Norm) : Node1322 :=
  node1322_of_cases (primitive_residual hBM hΩ hN) hGA hPairJ hOdd hKty hG2 hNF7U

end CFSG.RankThree.PartOne.N1322
