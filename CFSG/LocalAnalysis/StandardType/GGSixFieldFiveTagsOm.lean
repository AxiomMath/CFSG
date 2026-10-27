module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsOmMain
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmTag
public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin QuadraticMap LayerCores LayerFacts

section Tags

theorem ggFieldFiveNbrTag_POmegaPlus : GGFieldFiveNbrTag .POmegaPlus := by
  intro G _ _ n
  by_cases hn : 3 ≤ n
  · rw [show ggU .POmegaPlus n 1 = ⟨spinGroup (quadPlus n (GaloisField 2 1)),
        plusDatum n (GaloisField 2 1) hn⟩ from dite_eq_left hn]
    intro ψ G₀ hpres D hDel hDcard _ hDdiag x hxD L hL hLmark J hJ
    obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have hF : Nat.card (GaloisField 2 1) = 2 := by
      rw [GaloisField.card 2 1 one_ne_zero, pow_one]
    have hZ := RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := GaloisField 2 1) hn
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
      exact hker
    exact FieldFiveOm.fieldFive_om (nondegenerate_polarBilin_quadPlus n _) hF
      RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus_eq_commutator hn) hZ
      hinj hDel hDcard (fun d hd => LayerPDiv.exists_mem_ggConjPairs_of_inner
        (PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hDdiag d hd))) hxD hL hLmark hJ
  · rw [show ggU .POmegaPlus n 1 = trivialUniversal from dite_eq_right hn]
    intro ψ G₀ hpres
    exact absurd hpres.1.2 (by decide)

theorem ggFieldFiveNbrTag_POmegaMinus : GGFieldFiveNbrTag .POmegaMinus := by
  intro G _ _ n ψ G₀ hpres D hDel hDcard _ hDdiag x hxD L hL hLmark J hJ
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, -, hn⟩ := hadm
  subst hrange
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hZ := PsiDiag.SpinM.center_eq_bot (minusCoeffs_irr 2 1) hn
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  exact FieldFiveOm.fieldFive_om
    (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr 2 1)) hF
    (RootCentOmega.spinAction_quadMinus_injective (minusCoeffs_irr 2 1))
    (range_spinAction_quadMinus_eq_commutator hn (minusCoeffs_irr 2 1)) hZ hinj hDel hDcard
    (fun d hd => LayerPDiv.exists_mem_ggConjPairs_of_inner
      (PsiDiag.SpinM.exists_mem_centralizer (minusCoeffs_irr 2 1) hn ψ hker (hDdiag d hd)))
    hxD hL hLmark hJ

end Tags

section DropIn

theorem ggSixFieldFiveInput_of_e8 (hE8 : GGFieldFiveNbrTag .E8) : GGSixFieldFiveInput :=
  ggSixFieldFiveInput_of_omega_e8 ggFieldFiveNbrTag_POmegaPlus ggFieldFiveNbrTag_POmegaMinus hE8

end DropIn

end CFSG.StandardType
