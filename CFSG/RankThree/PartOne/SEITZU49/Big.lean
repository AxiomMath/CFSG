module

public import CFSG.RankThree.PartOne.SEITZU49.Root
public import CFSG.RankThree.PartOne.SEITZU49.Gen

public section

namespace CFSG.RankThree.PartOne.SEITZU49

theorem gen49Big_holds : Gen49Big := by
  intro f K _ _ _ hK hf6 h5 z hz hnz M hM
  obtain ⟨ω, -, hσω, hY⟩ := Root.Y_mem_Cset hK hf6 h5 hz hnz hM
  have hq : 2 ^ f ≠ 2 := by
    have : 2 ^ 6 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf6
    omega
  exact Gen.eq_top_of_Y_mem_Cset hK hq hz hM hσω hY

end CFSG.RankThree.PartOne.SEITZU49
