module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONSevenZero
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONSevenConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Dickson.I271 CFSG.ONSchreier

theorem on_isHeisCenter7_of_comm_involution
    {y : Pv} (hy7 : y ^ 7 = 1) (hy1 : y ≠ 1) {u : Pv} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huy : u * y = y * u) : IsHeisCenter7 y := by
  obtain ⟨g, k, hk, rfl⟩ := on_exists_conj_pow_on7W_zero hy7 hy1 hu2 hu1 huy
  exact (on_isHeisCenter7_on7W_zero.pow hk).conj g

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
