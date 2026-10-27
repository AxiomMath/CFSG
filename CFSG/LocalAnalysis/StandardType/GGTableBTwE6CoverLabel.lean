module

public import CFSG.LocalAnalysis.StandardType.GGTableBCoverMarked
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Marked
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Rep
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Abs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem largeEvenLabelAll_coverP_twE6
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBTwE6Row p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  have h1 := exists_marked_factorization_twE6 hp hlab hrow
  have h2 := fieldRepresentative_twE6 hp hlab hrow
  have h3 := absorption_twE6 hp hlab hrow
  refine LargeEvenLabelAll.mono ?_ (largeEvenLabelAll_and (largeEvenLabelAll_and h1 h2) h3)
  rintro R _ I F ⟨⟨⟨f, hmark, hfac⟩, hrep⟩, habs⟩
  exact ggTableB_assemble_of_bundle p F I ⟨f, hmark, hfac, hrep f hmark⟩ habs

end CFSG.StandardType
