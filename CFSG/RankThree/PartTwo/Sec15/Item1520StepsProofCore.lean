module

public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1521

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step1520Core_of (hcomm : Step1520Comm) (hcomp : Step1520CoreComp) : Step1520Core := by
  intro G _ _ A c L h Y hctx p P hP X hX hPX
  by_contra hno
  have hPA : P = ⁅P, A⁆ := hcomm G A c L h Y hctx p P hP
  have hPQ : P ∈ scriptQ A (lB A) := hP.2.2.2.2.2.1.1.1
  have hPD : P ≤ deltaZero A (lB A) X := le_deltaZero ⟨hPQ, hPA⟩ hPX
  obtain ⟨Y₀, hY₀, hPY₀, hnc⟩ := hcomp G A c L h Y hctx p P hP hPA X hX hPX hPD hno
  exact hnc (hP.2.2.2.2.2.2 Y₀ hY₀ P ⟨⟨hPQ, hPY₀⟩, hP.2.2.2.2.2.1.2⟩)

end CFSG.RankThree.PartTwo.Sec15
