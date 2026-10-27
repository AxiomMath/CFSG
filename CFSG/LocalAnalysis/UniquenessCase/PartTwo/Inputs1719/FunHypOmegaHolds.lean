module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmega
public import CFSG.ClassicalInvolution.ModelFacts.FundCentralizerNormalizer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunCommonModel
import CFSG.ClassicalInvolution.ModelFacts.FundTwinCommute
import CFSG.ClassicalInvolution.AschTight.HypOmegaGenCover
import CFSG.ClassicalInvolution.AschTight.HypOmegaGenSL2
import CFSG.ClassicalInvolution.Asc77.AscE189Comp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase (IsFundamentalOver)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ClassicalInvolution.ModelFacts (exists_isUniqueInvolution_of_mem_fundamentalSubgroups
  centralizer_le_normalizer_of_mem_fundamentalSubgroups
  commutator_eq_bot_of_mem_fundamentalSubgroups)
open CFSG.ClassicalInvolution.Disconnected.AschTight (commutator_map_eq_bot_of_mulEquiv_sl2
  mem_normalizer_map_of_centralizer_le_normalizer)


theorem k_FunHypOmega_holds : K_FunHypOmega := by
  intro X _ _ r q hr hr2 hdesc _ _ hL2 _ _
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨_, _, f, hadm, hqf, -⟩ := hdesc
  refine CFSG.ClassicalInvolution.Disconnected.AschTight.hypOmegaGen_of_mulEquiv_sl2_of_commute
    hr2 hadm.2.1 (fun g Kb hKb => isFundamentalOver_map_mulEquiv (MulAut.conj g) hKb)
    (fun Kb hKb => isFundamentalOver_mulEquiv_sl2 hr2 hqf hL2 hKb) ?_ ?_
  · intro K hK J hJ hne h2
    obtain ⟨t, n, hfund, hadm', -, ψ, -, hker, R, hR, R', hR', hRk, hR'k, rfl, rfl⟩ :=
      exists_common_model_of_isFundamentalOver hr2 hqf hL2 hK hJ
    have := CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 Fact.out hfund hadm'
    obtain ⟨z, hz⟩ := exists_isUniqueInvolution_of_mem_fundamentalSubgroups hr2 hfund hadm' hR
    obtain ⟨z', hz'⟩ := exists_isUniqueInvolution_of_mem_fundamentalSubgroups hr2 hfund hadm' hR'
    have hW := centralizer_le_normalizer_of_mem_fundamentalSubgroups hr2 hfund hadm' hR hz
    have hW' := centralizer_le_normalizer_of_mem_fundamentalSubgroups hr2 hfund hadm' hR' hz'
    have htwin : R ≠ R' → z = z' → ⁅R, R'⁆ = ⊥ := fun hRR hzz =>
      commutator_eq_bot_of_mem_fundamentalSubgroups hr2 hfund hadm' hR hR' hRR hz (hzz ▸ hz')
    have hf : 1 ≤ f := hadm'.2.1
    rcases
      CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
        hr2 hfund hadm' hR with h | ⟨-, h⟩
    · exact commutator_map_eq_bot_of_mulEquiv_sl2 ψ hker
        (CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hr2 hf)
        (Classical.choice h) hRk hR'k hz hz' hW hW' htwin hne h2
    · exact commutator_map_eq_bot_of_mulEquiv_sl2 ψ hker
        (CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hr2
          (by omega))
        (Classical.choice h) hRk hR'k hz hz' hW hW' htwin hne h2
  · intro K hK J hJ hne z hz v hv hvc hv2 hvz
    obtain ⟨t, n, hfund, hadm', -, ψ, -, hker, R, hR, R', hR', hRk, hR'k, rfl, rfl⟩ :=
      exists_common_model_of_isFundamentalOver hr2 hqf hL2 hK hJ
    have := CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 Fact.out hfund hadm'
    obtain ⟨z₀, hz₀⟩ := exists_isUniqueInvolution_of_mem_fundamentalSubgroups hr2 hfund hadm' hR
    obtain ⟨z₀', hz₀'⟩ := exists_isUniqueInvolution_of_mem_fundamentalSubgroups hr2 hfund hadm' hR'
    have hinj : ∀ x ∈ R, ψ x = 1 → x = 1 := fun x hxR hx1 =>
      Subgroup.mem_bot.mp (hRk ▸ Subgroup.mem_inf.mpr ⟨hxR, hx1⟩)
    obtain rfl : z = ψ z₀ :=
      hz.eq (CFSG.ClassicalInvolution.Asc77.isUniqueInvolution_map_of_injOn ψ hinj hz₀)
    exact mem_normalizer_map_of_centralizer_le_normalizer ψ hker hR'k hz₀ hz₀'
      (centralizer_le_normalizer_of_mem_fundamentalSubgroups hr2 hfund hadm' hR hz₀)
      (centralizer_le_normalizer_of_mem_fundamentalSubgroups hr2 hfund hadm' hR' hz₀') hv hvc hv2
      hvz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
