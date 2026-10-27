module

public import CFSG.RankThree.Theta.PlaneConditionSolvability
public import CFSG.RankThree.Theta.PartTwoLocalQuotientAlphaNormalizer

public section

namespace CFSG.RankThree.Theta

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThreeEvenClassification.Helpers
open CFSG.Assembly.RankThreeEven (aschCore)

variable {X : Type*} [Group X] [Finite X]

theorem part_two_solvable_local_quotient_alpha_criterion (A : Subgroup X)
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hquot : ∀ a ∈ A, a ≠ 1 →
      thetaAlpha 3 ((A.subgroupOf (centralizer ({a} : Set X))).map
          (QuotientGroup.mk' (centralLine a))) ≤
        aschbacherSolvableCore 3 (centralizer ({a} : Set X) ⧸ centralLine a)) :
    (∀ B : Subgroup X, B ≤ A → Nat.card B = 9 →
      Group.IsSolvable (thetaAlpha 3 B) ∧ Nat.Coprime 3 (Nat.card (thetaAlpha 3 B))) ∧
    (∀ B D : Subgroup X, B ≤ A → Nat.card B = 9 → D ≤ A → Nat.card D = 9 →
      thetaAlpha 3 B = thetaAlpha 3 D) ∧
    ∀ B : Subgroup X, B ≤ A → Nat.card B = 9 →
      aschCore 2 3 A ≤ normalizer (thetaAlpha 3 B : Set X) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have h27 : Nat.card A = 3 ^ 3 := by rw [hAcard]; norm_num
  have h9 : ∀ K : Subgroup X, Nat.card K = 9 → Nat.card K = 3 ^ 2 := fun K hK => by
    rw [hK]; norm_num
  have hlocal := (theta_plane_alpha_central_line_quotient_lifting hp A hA h27 hquot).1
  have hlocal' : ∀ c ∈ A, c ≠ 1 → ∀ E : Subgroup X, E ≤ A → Nat.card E = 3 ^ 2 →
      thetaPlaneAlpha 3 (E.subgroupOf (centralizer ({c} : Set X))) ≤
        solvablePrimeComplementCore (centralizer ({c} : Set X)) 3 := by
    intro c hc hc1 E hE hEcard
    rw [← thetaAlpha_eq_thetaPlaneAlpha hp,
      ← aschbacherSolvableCore_eq_solvablePrimeComplementCore hp]
    exact hlocal c hc hc1 E hE hEcard
  have hcond := thetaPlaneCondition_of_rank_three_local_planes 3 hp A hA h27 hlocal'
  have hplane : ∀ E : Subgroup X, E ≤ A → Nat.card E = 9 → ∀ e ∈ E, e ≠ 1 →
      ⁅inSubgroup (aschbacherSolvableCore 3) (centralizer (E : Set X)), A⁆ ≤
        inSubgroup (aschbacherSolvableCore 3) (centralizer ({e} : Set X)) := by
    intro E hE hEcard e he he1
    rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    exact hcond E hE (h9 E hEcard) e he he1
  obtain ⟨hind, hnorm⟩ := part_two_local_quotient_alpha_normalizer hp A hA h27 hquot
  refine ⟨fun B hBA hB => ?_, fun B D hBA hB hDA hD => hind B D hBA (h9 B hB) hDA (h9 D hD),
    fun B hBA hB => hnorm B hBA (h9 B hB)⟩
  obtain ⟨hs, hc, -⟩ :=
    part_two_plane_condition_solvability_and_comparison A hA hAcard hplane hBA hB hBA hB
  exact ⟨hs, hc⟩

end CFSG.RankThree.Theta
