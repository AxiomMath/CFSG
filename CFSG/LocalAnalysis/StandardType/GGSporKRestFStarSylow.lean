module

public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_fstar_isPGroup_of_normal_sylow {N : Type} [Group N] [Finite N] {p : ℕ}
    [Fact p.Prime] (hsolv : IsSolvable N) (S : Sylow p N) (hS : (S : Subgroup N).Normal)
    (hC : Subgroup.centralizer ((S : Subgroup N) : Set N) ≤ (S : Subgroup N)) :
    IsPGroup p ↥(CFSG.generalizedFitting N) := by
  haveI : Group.IsSolvable N := hsolv
  have hFS : CFSG.fittingSubgroup N ≤ (S : Subgroup N) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun q => ?_
    by_cases hq : (q : ℕ) = p
    · rw [hq]
      exact IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := p) (G := N)) S
    · haveI : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
      haveI : (S : Subgroup N).Normal := hS
      have hdisj : Disjoint (CFSG.pCore (q : ℕ) N) (S : Subgroup N) :=
        IsPGroup.disjoint_of_ne (q : ℕ) p hq _ _ (CFSG.pCore_isPGroup (p := (q : ℕ)) (G := N))
          (Sylow.isPGroup' S)
      have hcomm : ⁅CFSG.pCore (q : ℕ) N, (S : Subgroup N)⁆ = ⊥ := by
        refine le_bot_iff.mp ?_
        calc ⁅CFSG.pCore (q : ℕ) N, (S : Subgroup N)⁆
            ≤ CFSG.pCore (q : ℕ) N ⊓ (S : Subgroup N) := Subgroup.commutator_le_inf _ _
          _ ≤ ⊥ := le_of_eq hdisj.eq_bot
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hC
  rw [CFSG.WholeGroup.generalizedFitting_eq_fittingSubgroup_of_isSolvable]
  exact IsPGroup.to_le (Sylow.isPGroup' S) hFS

end CFSG.StandardType.SporadicShape
