module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.EmptyFaithful.S153G93DSizesCard

public section

namespace CFSG.Quasithin.S153G93D.Sizes

theorem modelSizes_holds : ModelSizes where
  sl := by
    intro W _ _ J d a h
    exact card_eq_binaryNaturalSL h
  sp4 := by
    intro W _ _ J a h
    exact card_eq_binaryNaturalSp4 h
  alt := by
    intro W _ _ J n h
    exact card_le_alternatingNatural h
  sym := by
    intro W _ _ J n h
    exact card_le_symmetricNatural h
  a7 := by
    intro W _ _ J h
    exact card_eq_a7Four h

end CFSG.Quasithin.S153G93D.Sizes
