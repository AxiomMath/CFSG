module

public import CFSG.Milestones.ASVolI.F411.Cent
public import CFSG.Milestones.ASVolI.F411.aL3Core

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable def burnsideF411a_projSLEquivStated (K : Type) [Field K] :
    projectiveSL 3 K ≃* StatedProj (StatedSL 3 K) :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 K)).trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K)

theorem burnsideF411a_autCentSylow_projSL3 (K : Type) [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] : burnsideF411_AutCentSylow (projectiveSL 3 K) p :=
  fun α S hα => burnsideF411a_projSL3_inner_of_fix_sylow p α S hα

theorem burnsideF411a_autCentSylow_L3 (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] : burnsideF411_AutCentSylow (StatedProj (StatedSL 3 K)) p := by
  haveI := burnsideF411a_finite_projSL (K := K) 3
  haveI : Finite (StatedProj (StatedSL 3 K)) :=
    Finite.of_equiv _ (burnsideF411a_projSLEquivStated K).toEquiv
  exact burnsideF411_autCentSylow_of_mulEquiv (burnsideF411a_projSLEquivStated K)
    (burnsideF411a_autCentSylow_projSL3 K p)

end CFSG.ASVolI
