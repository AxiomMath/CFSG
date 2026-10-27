module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowsAssembly
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowSpor

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)


structure K148OpenRowsLie : Prop where
  three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group
  nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf148 (projSL 3 (GaloisField 3 e))
  nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf148 (projSU 3 3 e)
  nine_G2 : RowSOf148 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group
  nine_SL4 : RowSOf148 (projSL 4 (GaloisField 3 1))
  nine_SU4 : RowSOf148 (projSU 4 3 1)

section Certs


theorem K148OpenRows.ofLie (O : K148OpenRowsLie) : K148OpenRows where
  three := O.three
  six_J3 := rowSOf148_j3
  six_McL := rowSOf148_mcl
  six_Suz := rowSOf148_suz
  six_ONan := rowSOf148_on
  six_Co3 := rowSOf148_co3
  six_HN := rowSOf148_hn
  six_Th := rowSOf148_th
  nine_SL3 := O.nine_SL3
  nine_SU3 := O.nine_SU3
  nine_G2 := O.nine_G2
  nine_SL4 := O.nine_SL4
  nine_SU4 := O.nine_SU4

end Certs

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
