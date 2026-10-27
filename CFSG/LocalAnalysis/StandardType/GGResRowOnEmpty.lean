module

public import CFSG.LocalAnalysis.StandardType.GGResRowOnDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBXDatumResOn_of_empty {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      ¬ S p lab) : GGTBXDatumResOn S := by
  intro G _ _ p B Bs x L D J y K hH _
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  refine ⟨fun hL => ?_, fun hK => ?_⟩
  · obtain ⟨lab, hlab, -, R, _, I, F, θ, hP, -⟩ := largeEvenMarking_exists_hasLabel hL
    exact absurd hP (hS p lab hp hp2 hlab)
  · obtain ⟨lab, hlab, -, R, _, I, F, θ, hP, -⟩ := largeEvenMarking_exists_hasLabel hK
    exact absurd hP (hS p lab hp hp2 hlab)

theorem ggPZNbrResDatumOn_of_empty {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      ¬ S p lab) : GGPZNbrResDatumOn S := by
  intro G _ _ p _ B Bs x L D J y K labJ labX X m z hprem Y hY hJY hBsY hnb hMark
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hprem.1.1.1.2.2.2.2.2.1.2.1
  obtain ⟨lab, hlab, -, R, _, I, F, θ, hP, -⟩ := largeEvenMarking_exists_hasLabel hMark
  exact absurd hP (hS p lab hp hp2 hlab)

end CFSG.StandardType

end
