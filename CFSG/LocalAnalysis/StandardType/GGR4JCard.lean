module

public import CFSG.LocalAnalysis.StandardType.GGR4JCardDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JFin
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentLSide

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggR4JInput_of_card (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hC : GGR4JCard) : GGR4JInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT y K hnbr hRG hSc _ hp3 Λ _ _ C b c V _ _ ι φ' h' α'
    hD hspan hcell hAL hAK
  obtain ⟨hcard, hlab⟩ := hC G p B Bs x L D J hcfg hOp hInn hNT y K hnbr hRG hSc hp3 Λ C b c V ι φ'
    h' α' hD hspan hcell hAL hAK
  refine ⟨?_, hlab⟩
  obtain ⟨hint, h48⟩ := ggR4J_finite_identity hp3 hD hspan hcell
  have hJL : J ≤ L := by
    subst hp3
    exact le_of_stdSub_left hcfg.2.2
  have hJK : J ≤ K := le_of_ggNbr hLB hcfg.1 hcfg.2.2 (hP G p B x L D J hcfg.1 hcfg.2.2) hnbr
  have hmono : ∀ {H H' : Subgroup G}, H ≤ H' → ggAutomizer H Bs ≤ ggAutomizer H' Bs := by
    intro H H' hHH'
    refine Subgroup.closure_mono ?_
    rintro φ ⟨g, hg, hgn, hφ⟩
    exact ⟨g, hHH' hg, hgn, hφ⟩
  have hle : ggAutomizer J Bs ≤
      Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ' (some j)) := by
    rw [← hint, ← hAL, ← hAK]
    exact le_inf (hmono hJL) (hmono hJK)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h48]; exact hcard)

end CFSG.StandardType

end
