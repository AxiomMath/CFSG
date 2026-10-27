module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunCommute
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunCommonModel
import CFSG.ClassicalInvolution.ModelFacts.FundTwinCommute
import CFSG.ClassicalInvolution.AschTight.HypOmegaGenCover
import CFSG.ClassicalInvolution.AschTight.HypOmegaGenSL2
public import CFSG.ClassicalInvolution.ModelFacts.FundCentralizerNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunSet

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase (IsFundamentalOver fundPred isFundamentalOver_map_mulEquiv)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL2Over17 IsReeOver17)
open CFSG.ClassicalInvolution.ModelFacts (exists_isUniqueInvolution_of_mem_fundamentalSubgroups
  centralizer_le_normalizer_of_mem_fundamentalSubgroups
  commutator_eq_bot_of_mem_fundamentalSubgroups)
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen
  commutator_map_eq_bot_of_mulEquiv_sl2 mem_normalizer_map_of_centralizer_le_normalizer)
open OddLie


theorem funSet_nonempty_of_lieModel {X : Type} [Group X] [Finite X] {r q : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2)
    (hdesc : ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n r f ∧ q = r ^ f ∧
      LieModel (X ⧸ Subgroup.center X) t n r f)
    (hqs : IsQuasisimple X) (hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) q)
    (hRee : ¬ IsReeOver17 X q) (hq3 : 3 < q) (P : Sylow 2 X) :
    (FunSet (fundPred q) X (P : Subgroup X)).Nonempty := by
  obtain ⟨t, n, f, hadm, hq, hX⟩ := hdesc
  have hqs : CFSG.Open.IsQuasisimple X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).mpr hqs
  have hfund := isFundTag_of_not_ree hr2 hadm hq hqs hX hRee
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    exact hL2 ⟨r, f, hr, hr2, hq, hadm.2.1, hX⟩
  have hq5 : 5 ≤ r ^ f := by
    obtain ⟨k, hk⟩ : Odd (r ^ f) := (hr.eq_two_or_odd'.resolve_left hr2).pow
    omega
  obtain ⟨ψ, hψs, hψk⟩ :=
    exists_cover_of_lieModel hr hr2 hfund hadm hqs hX (Or.inl ⟨hq5, hA1⟩)
  obtain ⟨γ, hγ⟩ := exists_isLongestRoot _
    (CFSG.LieType.HighestRoot.rank_pos_modelUniv t n r f hr hfund hadm)
  have hK₀ : IsFundamentalOver q
      (((CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).D.rootGroup γ ⊔
        (CFSG.ClassicalInvolution.Generic.modelUniv t n r f hr).D.rootGroup (-γ)).map ψ) :=
    ⟨t, n, r, f, hr, hr2, hq, hfund, hadm, ψ, hψs, hψk, _,
      ⟨1, γ, Or.inl hγ, (CFSG.ClassicalInvolution.Generic.conjSub_one _).symm⟩, rfl⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_funSet
    (𝔉 := fundPred q) (fun g _ hK => isFundamentalOver_map_mulEquiv (MulAut.conj g) hK) hK₀ P
  exact ⟨_, hg⟩

theorem hypOmegaGen_fundamental_of_lieModel
    {X : Type} [Group X] [Finite X] {r q : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2)
    (hdesc : ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n r f ∧ q = r ^ f ∧
      LieModel (X ⧸ Subgroup.center X) t n r f)
    (hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) q) :
    HypOmegaGen {Kb : Subgroup X | IsFundamentalOver q Kb} := by
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

theorem funSet_commute_of_lieModel
    {X : Type} [Group X] [Finite X] {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hdesc : ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n r f ∧ q = r ^ f ∧
      LieModel (X ⧸ Subgroup.center X) t n r f)
    (hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) q) (P : Sylow 2 X) {K₁ K₂ : Subgroup X}
    (hK₁ : K₁ ∈ FunSet (fundPred q) X (P : Subgroup X))
    (hK₂ : K₂ ∈ FunSet (fundPred q) X (P : Subgroup X)) (hne : K₁ ≠ K₂) :
    ⁅K₁, K₂⁆ = ⊥ :=
  commutator_eq_bot_of_mem_funSet (hypOmegaGen_fundamental_of_lieModel hr hr2 hdesc hL2) P hK₁
    hK₂ hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
