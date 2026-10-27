module

public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneIndependence

public section

namespace CFSG.RankThree.Theta

open CFSG CFSG.RankThree.LocalRank CFSG.RankThreeEvenClassification.Helpers

theorem theta_plane_alpha_hyperplane_independence {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (A : Subgroup X) (hA : CFSG.Assembly.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 3)
    (hlocal : ∀ c ∈ A, c ≠ 1 → ∀ E : Subgroup X, E ≤ A → Nat.card E = p ^ 2 →
      thetaAlpha p (E.subgroupOf (Subgroup.centralizer ({c} : Set X))) ≤
        aschbacherSolvableCore p (Subgroup.centralizer ({c} : Set X)))
    {B D : Subgroup X} (hBA : B ≤ A) (hB : Nat.card B = p ^ 2) (hDA : D ≤ A)
    (hD : Nat.card D = p ^ 2) :
    thetaAlpha p B = thetaAlpha p D := by
  have hlocal' : ∀ c ∈ A, c ≠ 1 → ∀ E : Subgroup X, E ≤ A → Nat.card E = p ^ 2 →
      thetaPlaneAlpha p (E.subgroupOf (Subgroup.centralizer ({c} : Set X))) ≤
        solvablePrimeComplementCore (Subgroup.centralizer ({c} : Set X)) p := by
    intro c hc hc1 E hE hEcard
    rw [← thetaAlpha_eq_thetaPlaneAlpha hp,
      ← aschbacherSolvableCore_eq_solvablePrimeComplementCore hp]
    exact hlocal c hc hc1 E hE hEcard
  rw [thetaAlpha_eq_thetaPlaneAlpha hp, thetaAlpha_eq_thetaPlaneAlpha hp]
  exact thetaPlaneAlpha_eq_of_rank_three_local_planes p hp A hA hAcard hlocal' B D hBA hDA hB hD

end CFSG.RankThree.Theta
