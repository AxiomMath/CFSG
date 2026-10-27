module

public import CFSG.Quasithin.EmptyFaithful.SzMSWTrans
public import CFSG.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin.SzMSW

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Pointwise

section Statement

variable {G : Type} [Group G]

@[expose] def IsC134Case4CorrW (G₀ R L : Subgroup G) : Prop :=
  IsC134Case4Corr G₀ R L ∧ MS93Case13W (c134Q G₀ L) L

@[expose] def IsC134CaseCorrW (i : ℕ) (G₀ R L : Subgroup G) : Prop :=
  match i with
  | 1 => IsC134Case1 G₀ R L
  | 2 => IsC134Case2 G₀ R L
  | 3 => IsC134Case3 G₀ R L
  | 4 => IsC134Case4CorrW G₀ R L
  | 5 => IsC134Case5 G₀ R L
  | _ => False

theorem IsC134CaseCorrW.corr {i : ℕ} {G₀ R L : Subgroup G} (h : IsC134CaseCorrW i G₀ R L) :
    IsC134CaseCorr i G₀ R L :=
  match i, h with
  | 0, h => h
  | 1, h => h
  | 2, h => h
  | 3, h => h
  | 4, h => h.1
  | 5, h => h
  | _ + 6, h => h

end Statement

variable {G : Type} [Group G] [Finite G]

end CFSG.Quasithin.SzMSW
