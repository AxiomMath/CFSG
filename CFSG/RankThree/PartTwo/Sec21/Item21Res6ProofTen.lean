module

public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofStatements
import CFSG.RankThree.PartTwo.Sec6.Item68

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def Item2110JTheta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∀ J ∈ thetaComponentsAt 3 d, d ∈ J →
        J = iOf218 L d ⊔ inSubgroup (aschbacherSolvableCore 3) J

namespace Item21Res6Proof

variable {G : Type} [Group G]

theorem le_normalizer_of_unique [Finite G] {d : G} {J : Subgroup G}
    (hJ : J ∈ thetaComponentsAt 3 d) (hdJ : d ∈ J)
    (huniq : ∀ J' : Subgroup G, J' ∈ thetaComponentsAt 3 d ∧ d ∈ J' → J' = J) :
    Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine huniq _ ⟨Sec6.map_conj_mem_thetaComponentsAt hg hJ, ?_⟩
  refine ⟨d, hdJ, ?_⟩
  change g * d * g⁻¹ = d
  rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]

theorem sup_theta_eq [Finite G] {d : G} {I J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 d)
    (hJI : J = I ⊔ inSubgroup (aschbacherSolvableCore 3) J) :
    I ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)) =
      J ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)) := by
  have hθ : inSubgroup (aschbacherSolvableCore 3) J ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)) := by
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hJ]
    exact inf_le_right
  apply le_antisymm
  · exact sup_le_sup_right (hJI ▸ le_sup_left) _
  · refine sup_le ?_ le_sup_right
    rw [hJI]
    exact sup_le le_sup_left (hθ.trans le_sup_right)

end Item21Res6Proof

open Item21Res6Proof

theorem item2110One_of (h3 : Item2110Three) (hJ : Item2110JTheta) : Item2110One := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdc
  obtain ⟨J, ⟨hJd, hdJ⟩, huniq⟩ := h3 G A E U c L hpair hL d hdA hd1 hdc
  have hJI := hJ G A E U c L hpair hL d hdA hd1 hdc J hJd hdJ
  rw [sup_theta_eq hJd hJI]
  exact le_trans (le_inf (le_normalizer_of_unique hJd hdJ huniq)
    (Sec6.le_normalizer_theta _)) (Subgroup.inf_normalizer_le_normalizer_sup _ _)

end CFSG.RankThree.PartTwo.Sec21
