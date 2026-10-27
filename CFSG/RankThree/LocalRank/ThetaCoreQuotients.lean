module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer

public section

namespace CFSG.RankThree.LocalRank

open CFSG CFSG.RankThreeEvenClassification.Helpers

theorem solvable_prime_complement_core_quotient_centralizers {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] (hNs : Group.IsSolvable N)
    (hNp : ¬p ∣ Nat.card N) :
    N ≤ aschbacherSolvableCore p G ∧
    (aschbacherSolvableCore p G).map (QuotientGroup.mk' N) = aschbacherSolvableCore p (G ⧸ N) ∧
    aschbacherSolvableCore p (G ⧸ aschbacherSolvableCore p G) = ⊥ ∧
    ∀ A : Subgroup G, IsPGroup p A →
      (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer (A : Set G))).map
          (QuotientGroup.mk' N) =
        inSubgroup (aschbacherSolvableCore p)
          (Subgroup.centralizer (A.map (QuotientGroup.mk' N) : Set (G ⧸ N))) := by
  have hmapGen : ∀ (M : Subgroup G) [M.Normal], Group.IsSolvable M → ¬p ∣ Nat.card M →
      (aschbacherSolvableCore p G).map (QuotientGroup.mk' M) =
        aschbacherSolvableCore p (G ⧸ M) := by
    intro M _ hMs hMp
    have hker : (QuotientGroup.mk' M).ker = M := QuotientGroup.ker_mk' M
    rw [aschbacherSolvableCore_eq_solvablePrimeComplementCore hp G,
      aschbacherSolvableCore_eq_solvablePrimeComplementCore hp (G ⧸ M)]
    exact solvablePrimeComplementCore_map_eq_of_solvable_prime_complement_kernel p hp _
      (QuotientGroup.mk'_surjective M) (by rw [hker]; exact hMs) (by rw [hker]; exact hMp)
  obtain ⟨hθs, -, hθp, hmax, -⟩ := solvable_prime_complement_core_characterization (H := G) hp
  refine ⟨hmax N inferInstance hNs hNp, hmapGen N hNs hNp, ?_, fun A hA => ?_⟩
  · rw [← hmapGen (aschbacherSolvableCore p G) hθs hθp]
    exact (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' _).ge
  · have hker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
    rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    exact thetaCoreOf_centralizer_map_eq_of_pGroup_solvable_prime_complement_kernel p hp _
      (QuotientGroup.mk'_surjective N) (by rw [hker]; exact hNs) (by rw [hker]; exact hNp) A hA

end CFSG.RankThree.LocalRank
