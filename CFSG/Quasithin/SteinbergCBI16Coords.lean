module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.SteinbergCB.I16

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def projOdd (k : ℕ) : (Fin (k + 1) → ZMod 2) →+ (Fin k → ZMod 2) where
  toFun x j := x j.castSucc
  map_zero' := rfl
  map_add' _ _ := rfl

@[expose] def inclOdd (k : ℕ) : (Fin k → ZMod 2) →+ (Fin (k + 1) → ZMod 2) where
  toFun y i := if h : i.val < k then y ⟨i, h⟩ else ∑ j, y j
  map_zero' := by
    funext i
    simp
  map_add' y y' := by
    funext i
    simp only [Pi.add_apply]
    split_ifs
    · rfl
    · exact Finset.sum_add_distrib

@[expose] def projEven (k : ℕ) : (Fin (k + 2) → ZMod 2) →+ (Fin k → ZMod 2) where
  toFun x j := x (Fin.castAdd 2 j) + x (Fin.last (k + 1))
  map_zero' := by
    funext j
    simp
  map_add' x x' := by
    funext j
    simp only [Pi.add_apply]
    abel

@[expose] def inclEven (k : ℕ) : (Fin k → ZMod 2) →+ (Fin (k + 2) → ZMod 2) where
  toFun y i := if h : i.val < k then y ⟨i, h⟩ else if i.val = k then ∑ j, y j else 0
  map_zero' := by
    funext i
    simp
  map_add' y y' := by
    funext i
    simp only [Pi.add_apply]
    split_ifs
    · rfl
    · exact Finset.sum_add_distrib
    · exact (add_zero 0).symm

end CFSG.Quasithin.SteinbergCB.I16
