module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelected
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate8032
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPosition
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfType
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRes

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem guardedLargeEvenLabel_of_coordB {n p : ℕ} (hn : 4 ≤ n) {lab : LargeEvenLabel}
    (h : GGSecFiveBCoordBLabel n p lab) : GuardedLargeEvenLabel lab := by
  unfold GGSecFiveBCoordBLabel at h
  unfold GuardedLargeEvenLabel
  rcases h with ⟨hBC, hr, -⟩ | ⟨ht, hr, -⟩ | ⟨ht, hr, -⟩ | ⟨ht, hr, hf, -⟩
  · exact Or.inl ⟨hBC, by omega⟩
  · exact Or.inr (Or.inl ⟨Or.inr ht, by omega⟩)
  · exact Or.inr (Or.inl ⟨Or.inl ht, by omega⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨ht, by omega, hf⟩))

end CFSG.StandardType

end
