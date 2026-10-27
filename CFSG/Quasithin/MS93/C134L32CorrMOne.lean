module

public import CFSG.Quasithin.MS93.ASC134
public import CFSG.Quasithin.Background.C134L32CorrM

public section

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped Pointwise

namespace CFSG.Quasithin.MS93.IsC134CaseCorr

theorem toLocal {G : Type} [Group G] {i : ℕ} {G₀ R L : Subgroup G}
    (h : _root_.CFSG.Quasithin.MS93.IsC134CaseCorr i G₀ R L) :
    _root_.CFSG.Quasithin.C134CorrLocal.IsC134CaseCorr i G₀ R L := by
  match i, h with
  | 1, h => exact h
  | 2, h => exact h
  | 3, h => exact h
  | 4, h => exact h
  | 5, h => exact h

theorem toCaseM {G : Type} [Group G] {i : ℕ} {G₀ R L : Subgroup G}
    (h : _root_.CFSG.Quasithin.MS93.IsC134CaseCorr i G₀ R L) :
    _root_.CFSG.Quasithin.IsC134CaseM i G₀ R L :=
  _root_.CFSG.Quasithin.IsC134CaseM.of_corr (toLocal h)

end CFSG.Quasithin.MS93.IsC134CaseCorr

