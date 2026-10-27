module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkSplit
public import CFSG.LocalAnalysis.StandardType.GGForkAffineFork
public import CFSG.LocalAnalysis.StandardType.GGForkAffineCells
public import CFSG.LocalAnalysis.StandardType.GGForkClassify

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggForkAffineExclRest_of_tbSpan (hS : GGTBSpanInput) : GGForkAffineExclRest := by
  intro G _ _ p B Bs x L D J hC hO hI hNT y K hN hR hPm _ Λ _ _ M C V _ _ ι φ φa h α ha αa
    b c hM hCM hF hlin hlina hind hL hK hSA hSB
  have hp2 : p ≠ 2 := hC.1.2.2.2.2.2.1.2.1
  have hspan := hS G p B Bs x L D J hC hO hI hNT y K hN hR hPm Λ M C V ι φ φa h α ha αa b c
    hM hCM hF hlin hlina hind hL hK
  have hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs := fun i =>
    mem_ggInduced_top_of_mem_ggAutomizer (H := L)
      (by rw [hL]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hφa : φa ∈ ggInduced ⊤ Bs :=
    mem_ggInduced_top_of_mem_ggAutomizer (H := K)
      (by rw [hK]; exact Subgroup.subset_closure (Or.inr rfl))
  obtain ⟨h1, h2⟩ := ggForkRest_classify hM hCM hF.toMatrix hSA hSB
  refine ⟨fun _ => h1, fun hu => ?_⟩
  rcases h2 with h2 | h2
  · exact h2
  · exfalso
    obtain ⟨D'⟩ :=
      ggReflDatum_of_fork_one hp2 hNT ι hF hφ hφa hlin hlina hind hspan hu
    exact ggForkAffineCell_false hp2 hNT D' h2

end CFSG.StandardType
