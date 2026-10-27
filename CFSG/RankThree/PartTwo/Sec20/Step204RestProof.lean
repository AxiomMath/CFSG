module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

theorem step204Rest_of (hcyc : Step204Cyclic) (h1411 : Step204Asc1411)
    (hfinal : Step204Final) : Step204Rest := by
  intro G _ _ A M L N c T i j P hset X hX
  by_contra hXM
  have hm := hcyc G A M L N c T i j P hset X hX hXM
  by_cases hL2 : ∃ m : ℕ, Nonempty (↥(yAlpha M X T c) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 m))
  · exact hfinal G A M L N c T i j P hset X hX hXM hm (Or.inr (Or.inr hL2))
  · push Not at hL2
    have hcov := h1411 G A M L N c T i j P hset X hX hXM hm fun m h => (hL2 m).elim h.some
    exact hfinal G A M L N c T i j P hset X hX hXM hm (hcov.imp_right Or.inl)

end CFSG.RankThree.PartTwo.Sec20
