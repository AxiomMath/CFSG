module

public import CFSG.Quasithin.EmptyFaithful.A38c15IrrBasic
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrMono
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrCyc
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrHess
public import CFSG.RankThree.PartOne.S12.InputsLinear

public section

namespace CFSG.Quasithin.A38c15

open CFSG.RankThree.PartOne CFSG.RepresentationTheory

theorem sl3OddIrr_of_bm (hBM : ExtBloomMitchell) (hN6 : N1322.KF1322ThreeA6Norm) :
    SL3OddIrr := by
  intro p _ hp2 M hodd hirr
  have hG := glImage_irreducible hirr
  obtain ⟨H, hHG, hnorm, hHirr, hcases⟩ := hBM p hp2 hG
  rcases hcases with h1 | ⟨M₀, hMt, hdet, hH⟩ | ⟨hA5, -, hdec, -⟩ | ⟨hL, hp7⟩ |
    ⟨hperf, hZ, hA6, hp30⟩ | ⟨hcyc, -, -⟩ | ⟨hcard, hext, -⟩ | ⟨hHG', hmono⟩
  · left
    exact eq_top_of_stated_le_glImage (h1 ▸ hHG)
  · exfalso
    subst hH
    exact false_of_omega hp2 hodd hMt hdet hnorm hHirr
  · exfalso
    obtain ⟨e⟩ := hA5
    exact false_of_alt5 hp2 hodd hHG hHirr e hdec
  · exfalso
    obtain ⟨e⟩ := hL
    have hp7' : p ≠ 7 := by omega
    exact false_of_gl32 hp2 hp7' hodd hHG hnorm hHirr e
  · exfalso
    exact false_of_threeA6 hN6 hp2 hodd hHG hnorm hHirr hperf hZ hA6 hp30
  · right
    exact isSolvable_of_glImage (isSolvable_of_cyclic_normal hHG hnorm hHirr hcyc)
  · right
    exact isSolvable_of_glImage
      (isSolvable_of_extraspecial27_normal hHG hnorm hHirr hcard hext)
  · right
    subst hHG'
    exact isSolvable_of_glImage (isSolvable_of_isTransitiveMonomial hmono)

end CFSG.Quasithin.A38c15
