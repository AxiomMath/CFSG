
module

public import CFSG.Quasithin.Background.A3Structure36BSetupBase

public import CFSG.Quasithin.Background.A3Structure36BPrimeData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

variable {X : Type} [Group X]

theorem exists_kernelSetup (hF : A36CaseBFacts) (h : A36BHyp X) :
    ∃ K : Subgroup X, KernelSetup X K := by
  obtain ⟨q₀, hq₀, hπ₀⟩ := exists_isPi h
  obtain ⟨D₀⟩ := exists_primeData hF.a129 h hq₀ hπ₀
  obtain ⟨r, hr, h5, hsl⟩ := D₀.exists_sl2 h hq₀ hπ₀
  have := D₀.normal_K
  obtain ⟨hKD₀, hPSL⟩ := isKernelData_of_sl2 h hr h5 hsl
  refine ⟨D₀.K, hKD₀, ⟨r, hr, h5, hPSL⟩, ⟨r, hr, h5, exists_hom_of_isSL2 hsl⟩,
    fun p hp hπ => ?_⟩
  obtain ⟨D⟩ := exists_primeData hF.a129 h hp hπ
  obtain ⟨r', hr', h5', hsl'⟩ := D.exists_sl2 h hp hπ
  have := D.normal_K
  obtain ⟨hKD, -⟩ := isKernelData_of_sl2 h hr' h5' hsl'
  exact ⟨D, kernel_eq hF.l2mult h hr h5 hPSL hKD hKD₀⟩

end CFSG.Quasithin.A36B
