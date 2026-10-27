module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunLowerBound
public import CFSG.ClassicalInvolution.RouteD.MultiStarModel
import CFSG.ClassicalInvolution.Uniform.U3Edge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFundPairs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieCover
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunFamily
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie
open F14


theorem exists_commuting_modelFund_of_funTwoType {p : ℕ} [Fact p.Prime] {t : StatedLieTag}
    {n f : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (htwo : FunTwoType t n) :
    ∃ R ∈ ModelFund p t n f, ∃ S ∈ ModelFund p t n f, Commutes R S := by
  by_cases hG2 : t = .G2
  · subst t; exact exists_commuting_fund_g2 hadm
  by_cases hD4 : t = .trialityD4
  · subst t; exact exists_commuting_fund_trialityD4 hadm
  have hfund : IsFundTag t := by cases t <;> simp_all [FunTwoType, IsFundTag]
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    simp [FunTwoType] at htwo
  have h3 : ¬ ((t = .PSL ∧ n = 3) ∨ (t = .PSU ∧ n = 3)) := by
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [FunTwoType] at htwo
  obtain ⟨γ, hγ⟩ := exists_isLongestRoot _
    (CFSG.LieType.HighestRoot.rank_pos_modelUniv t n p f Fact.out hfund hadm)
  have hR : ((modelUniv t n p f Fact.out).D.rootGroup γ ⊔
      (modelUniv t n p f Fact.out).D.rootGroup (-γ)) ∈ ModelFund p t n f :=
    ⟨1, γ, Or.inl hγ, (conjSub_one _).symm⟩
  exact CFSG.ClassicalInvolution.Uniform.exists_commuting_fund
    hp2 hfund hadm hG2 hD4 hA1 h3 hR

theorem two_le_ncard_funSet_of_funTwoType {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : CFSG.Blueprint.LieModel X t n p f)
    (htwo : FunTwoType t n) (P : Sylow 2 X) :
    2 ≤ (FunSet (fundPred (p ^ f)) X (P : Subgroup X)).ncard := by
  have : Fact p.Prime := ⟨hp⟩
  have hfund : IsFundTag t := by cases t <;> simp_all [FunTwoType, IsFundTag]
  obtain ⟨R, hR, S, hS, hc⟩ := exists_commuting_modelFund_of_funTwoType hp2 hadm htwo
  obtain ⟨ψ, hψs, hψk⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p f hp hp2 hfund hadm X hX
  have hne : R.map ψ ≠ S.map ψ := by
    rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
        hp2 hfund hadm hR with h | ⟨_, h⟩
    · exact F14.map_ne_of_commuting_of_equiv_sl2 ψ hψk (Classical.choice h) hc
    · exact F14.map_ne_of_commuting_of_equiv_sl2 ψ hψk (Classical.choice h) hc
  let K : Fin 2 → Subgroup X := ![R.map ψ, S.map ψ]
  have hK : ∀ i, IsFundamentalOver (p ^ f) (K i) := by
    intro i
    have key : ∀ A ∈ ModelFund p t n f, IsFundamentalOver (p ^ f) (A.map ψ) :=
      fun A hA => ⟨t, n, p, f, hp, hp2, rfl, hfund, hadm, ψ, hψs, hψk, A, hA, rfl⟩
    fin_cases i
    · exact key _ hR
    · exact key _ hS
  have hinj : Function.Injective K := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | rfl | exact (hne hij).elim | exact (hne hij.symm).elim
  have hcomm : ∀ i j, i ≠ j → Commutes (K i) (K j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim |
      exact CFSG.ClassicalInvolution.Asc77.ih8_commutes_map ψ hc |
      exact (CFSG.ClassicalInvolution.Asc77.ih8_commutes_map ψ hc).symm
  have hnorm : ∀ i j, K j ≤ Subgroup.normalizer (K i : Set X) := by
    intro i j
    by_cases hij : i = j
    · subst j; exact Subgroup.le_normalizer
    · exact (show K j ≤ Subgroup.centralizer (K i : Set X) from
        fun b hb => Subgroup.mem_centralizer_iff.mpr fun a ha =>
          hcomm i j hij a ha b hb).trans (Subgroup.centralizer_le_normalizer _)
  have h := F14.natCard_le_ncard_funSet_of_normalizing_family
    (𝔉 := fundPred (p ^ f))
    (fun g _ hK => isFundamentalOver_map_mulEquiv (MulAut.conj g) hK) K hK hinj hnorm P
  simpa using h

end CFSG.LocalAnalysis.UniquenessCase.UC22
