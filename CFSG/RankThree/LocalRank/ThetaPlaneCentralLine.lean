module

public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaRankThree

public section

namespace CFSG.RankThree.LocalRank

open CFSG CFSG.RankThreeEvenClassification.Helpers

variable {X : Type*} [Group X]

@[expose] def centralLine (a : X) : Subgroup (Subgroup.centralizer ({a} : Set X)) :=
  Subgroup.zpowers ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem centralLine_le_center (a : X) :
    centralLine a ≤ Subgroup.center (Subgroup.centralizer ({a} : Set X)) := by
  apply Subgroup.zpowers_le.mpr
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)

instance centralLine_normal (a : X) : (centralLine a).Normal :=
  normal_of_le_center _ (centralLine_le_center a)

theorem theta_plane_alpha_central_line_quotient_lifting [Finite X] {p : ℕ} (hp : p.Prime)
    (A : Subgroup X) (hA : CFSG.Assembly.IsElemAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hquot : ∀ a ∈ A, a ≠ 1 →
      thetaAlpha p ((A.subgroupOf (Subgroup.centralizer ({a} : Set X))).map
          (QuotientGroup.mk' (centralLine a))) ≤
        aschbacherSolvableCore p (Subgroup.centralizer ({a} : Set X) ⧸ centralLine a)) :
    (∀ a ∈ A, a ≠ 1 → ∀ E : Subgroup X, E ≤ A → Nat.card E = p ^ 2 →
      thetaAlpha p (E.subgroupOf (Subgroup.centralizer ({a} : Set X))) ≤
        aschbacherSolvableCore p (Subgroup.centralizer ({a} : Set X))) ∧
    ∀ a ∈ A, a ≠ 1 →
      Nat.card ((A.subgroupOf (Subgroup.centralizer ({a} : Set X))).map
        (QuotientGroup.mk' (centralLine a))) = p ^ 2 ∧
      A.subgroupOf (Subgroup.centralizer ({a} : Set X)) ⊓
        (QuotientGroup.mk' (centralLine a)).ker = centralLine a := by
  have : Fact p.Prime := ⟨hp⟩
  have common : ∀ a ∈ A, a ≠ 1 →
      A ≤ Subgroup.centralizer ({a} : Set X) ∧
      (QuotientGroup.mk' (centralLine a)).ker ≤ A.subgroupOf (Subgroup.centralizer ({a} : Set X)) ∧
      Nat.card (QuotientGroup.mk' (centralLine a)).ker = p ∧
      Nat.card (A.subgroupOf (Subgroup.centralizer ({a} : Set X))) = p ^ 3 := by
    intro a ha ha1
    have hAC := commutative_plane_le_element_centralizer A hA.1 a ha
    refine ⟨hAC, ?_, ?_, ?_⟩
    · rw [QuotientGroup.ker_mk']
      apply Subgroup.zpowers_le.mpr
      exact Subgroup.mem_subgroupOf.mpr ha
    · rw [QuotientGroup.ker_mk', centralLine, Nat.card_zpowers, Subgroup.orderOf_mk]
      exact orderOf_eq_prime (hA.2 a ha) ha1
    · rw [← hAcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
  refine ⟨fun a ha ha1 E hE hEcard => ?_, fun a ha ha1 => ?_⟩
  · obtain ⟨hAC, hkerLe, hkerCard, hactorCard⟩ := common a ha ha1
    have hcentral : (QuotientGroup.mk' (centralLine a)).ker ≤
        Subgroup.center (Subgroup.centralizer ({a} : Set X)) := by
      rw [QuotientGroup.ker_mk']
      exact centralLine_le_center a
    have hplaneLe : E.subgroupOf (Subgroup.centralizer ({a} : Set X)) ≤
        A.subgroupOf (Subgroup.centralizer ({a} : Set X)) := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hE (Subgroup.mem_subgroupOf.mp hx))
    have hcomm : IsMulCommutative (E.subgroupOf (Subgroup.centralizer ({a} : Set X))) :=
      elementary_plane_commutative_of_le p _ _
        (isElemAbelian_subgroupOf p A (Subgroup.centralizer ({a} : Set X)) hA) hplaneLe
    have hplaneCard : Nat.card (E.subgroupOf (Subgroup.centralizer ({a} : Set X))) = p ^ 2 := by
      rw [← hEcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hE.trans hAC)).toEquiv
    have halpha := hquot a ha ha1
    rw [thetaAlpha_eq_thetaPlaneAlpha hp,
      aschbacherSolvableCore_eq_solvablePrimeComplementCore hp] at halpha
    rw [thetaAlpha_eq_thetaPlaneAlpha hp, aschbacherSolvableCore_eq_solvablePrimeComplementCore hp]
    exact thetaPlaneAlpha_le_of_rank_three_quotient_actor p hp _ (QuotientGroup.mk'_surjective _)
      hcentral hkerCard _ _ hplaneLe hkerLe hcomm hplaneCard hactorCard halpha
  · obtain ⟨-, hkerLe, hkerCard, hactorCard⟩ := common a ha ha1
    refine ⟨rank_three_actor_map_card p hp _ _ hkerLe hkerCard hactorCard, ?_⟩
    rw [inf_eq_right.mpr hkerLe, QuotientGroup.ker_mk']

end CFSG.RankThree.LocalRank
