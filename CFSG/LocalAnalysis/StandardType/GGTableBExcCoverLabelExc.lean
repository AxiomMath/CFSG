module

public import CFSG.LocalAnalysis.StandardType.GGTableBCoverMarked
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcMarked
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRep
public import CFSG.LocalAnalysis.StandardType.GGTableBExcAbs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem largeEvenLabelAll_coverP_excInn
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBExcInnRow p lab ∨ GGL48TBExcTwoRow p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  have h1 := exists_marked_factorization_exc hp hlab
    (hrow.elim Or.inl fun h => Or.inr (Or.inr h))
  have h2 := fieldRepresentative_exc hp hlab (hrow.elim Or.inl fun h => Or.inr (Or.inl h))
  have h3 := absorption_exc hlab hrow
  refine LargeEvenLabelAll.mono ?_ (largeEvenLabelAll_and (largeEvenLabelAll_and h1 h2) h3)
  rintro R _ I F ⟨⟨⟨f, hmark, hfac⟩, hrep⟩, habs⟩
  exact ggTableB_assemble_of_bundle p F I ⟨f, hmark, hfac, hrep f hmark⟩ habs

end CFSG.StandardType
