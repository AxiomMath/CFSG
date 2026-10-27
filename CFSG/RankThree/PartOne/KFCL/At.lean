module

public import CFSG.RankThree.PartOne.KFCL.GenDefs
public import CFSG.RankThree.PartOne.S15K.CovAt

public section

namespace CFSG.RankThree.PartOne.KFCL

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne

theorem kfAtRow_of_allSplit (hAll : S15K.KF158AllSplit) {r : ℕ} (hr1 : 1 ≤ r) (hr3 : r ≤ 3) :
    KFAtRow r := by
  intro G _ _ p A c L E h15 hF _ hout t ht
  have hout' : Outcome152One p E A (lieGenerated p E) ∨ Outcome152Two p E A (lieGenerated p E) ∨
      Outcome152Three p E A (lieGenerated p E) := by
    interval_cases r
    · exact Or.inl hout
    · exact Or.inr (Or.inl hout)
    · exact Or.inr (Or.inr hout)
  obtain ⟨g, -, hKF⟩ := hAll G p A c L E h15 hF hout' t ht
  exact ⟨g, hKF⟩

theorem kfAtEven_of_allSplit (hAll : S15K.KF158AllSplit) (h4 : KFAtRow 4) : KFAtEven :=
  kfAtEven_of_rows (kfAtRow_of_allSplit hAll le_rfl (by norm_num))
    (kfAtRow_of_allSplit hAll (by norm_num) (by norm_num))
    (kfAtRow_of_allSplit hAll (by norm_num) le_rfl) h4

end CFSG.RankThree.PartOne.KFCL
