module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaQuotient

public section

namespace CFSG.RankThree.GroupTheory

open CFSG CFSG.RankThree.LocalRank

theorem central_quotient_solvable_prime_complement_core {X Y : Type*} [Group X] [Group Y]
    [Finite X] [Finite Y] {p : ℕ} (hp : p.Prime) (f : X →* Y) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center X) :
    (aschbacherSolvableCore p X).map f = aschbacherSolvableCore p Y := by
  rw [aschbacherSolvableCore_eq_solvablePrimeComplementCore hp X,
    aschbacherSolvableCore_eq_solvablePrimeComplementCore hp Y]
  exact RankThreeEvenClassification.Helpers.solvablePrimeComplementCore_map_eq_of_central_kernel p
    hp f hf hker

end CFSG.RankThree.GroupTheory
