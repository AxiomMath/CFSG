module

public import CFSG.Holt.H78.Theorem1
public import CFSG.Holt.H78.Bridge
public import CFSG.RankThree.GF2n.Smith81.Sec217NoSE
public import CFSG.RankThree.GF2n.Smith81.Sec217Block
public import CFSG.RankThree.GF2n.Smith81.Sec217NoAlt

public section

namespace CFSG.RankThree.GF2n.Smith81

section Exclude


theorem smith217Exclude_holds : Smith217ExcludeStatement := by
  intro G _ _ M Q Z B _ hc
  rintro (⟨M', hM'⟩ | ⟨n, -, ⟨e⟩⟩)
  · exact not_stronglyEmbedded_fstar M Q Z B hc ⟨M', hM'⟩
  · exact not_nonempty_equiv_alternatingGroup hc n ⟨e⟩

end Exclude

section Connected

theorem smith217_holds : Smith217Statement :=
  smith217_of_holt
      (CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1)
      smith217UniqueBlock smith217Exclude_holds

end Connected

end CFSG.RankThree.GF2n.Smith81
