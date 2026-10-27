module

public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneExactQuotient
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaRankThree

public section

namespace CFSG.RankThree.LocalRank

open CFSG CFSG.RankThreeEvenClassification.Helpers

theorem theta_plane_alpha_exact_prime_kernel_quotients {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (B : Subgroup G) (hB : CFSG.Assembly.IsElemAbelian p B)
    (hBcard : Nat.card B = p ^ 2) (N : Subgroup G) [N.Normal]
    (hN : (Group.IsSolvable N ∧ ¬p ∣ Nat.card N) ∨
      (N ≤ Subgroup.center G ∧ IsPGroup p N ∧ N ⊓ B = ⊥)) :
    Nat.card (B.map (QuotientGroup.mk' N)) = p ^ 2 ∧
    (thetaT p B).map (QuotientGroup.mk' N) = thetaT p (B.map (QuotientGroup.mk' N)) ∧
    (thetaJ p B).map (QuotientGroup.mk' N) = thetaJ p (B.map (QuotientGroup.mk' N)) ∧
    (thetaAlpha p B).map (QuotientGroup.mk' N) = thetaAlpha p (B.map (QuotientGroup.mk' N)) ∧
    (N ≤ Subgroup.center G → IsPGroup p N → N ⊓ B = ⊥ →
      (thetaAlpha p B ≤ aschbacherSolvableCore p G ↔
        thetaAlpha p (B.map (QuotientGroup.mk' N)) ≤ aschbacherSolvableCore p (G ⧸ N))) := by
  set π := QuotientGroup.mk' N with hπ
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hBpg : IsPGroup p B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g g.2)⟩
  have hne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hBcard
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hcentralCase : N ≤ Subgroup.center G → IsPGroup p N → N ⊓ B = ⊥ →
      π.ker ≤ Subgroup.center G ∧ IsPGroup p π.ker ∧ Set.InjOn π (B : Set G) := by
    intro hNc hNpg hNB
    refine ⟨by rw [hker]; exact hNc, by rw [hker]; exact hNpg, injOn_of_disjoint_kernel π B ?_⟩
    rw [hker, disjoint_iff, inf_comm]
    exact hNB
  have key : Set.InjOn π (B : Set G) ∧
      (thetaPlaneIntersection p B).map π = thetaPlaneIntersection p (B.map π) ∧
      ∀ c ∈ B, c ≠ 1 → (thetaCoreOf p (Subgroup.centralizer ({c} : Set G))).map π =
        thetaCoreOf p (Subgroup.centralizer ({π c} : Set (G ⧸ N))) := by
    rcases hN with ⟨hNs, hNp⟩ | ⟨hNc, hNpg, hNB⟩
    · have hkS : Group.IsSolvable π.ker := by rw [hker]; exact hNs
      have hkP : ¬p ∣ Nat.card π.ker := by rw [hker]; exact hNp
      have hinj := injOn_pSubgroup_of_prime_complement_kernel p hp π hkP B hBpg
      exact ⟨hinj, thetaPlaneIntersection_map_eq_of_solvable_prime_complement_kernel p hp π hsurj
        hkS hkP B hBpg hinj, fun c hc _ =>
          thetaCoreOf_element_centralizer_map_eq_of_solvable_prime_complement_kernel p hp π hsurj
            hkS hkP B hBpg c hc⟩
    · obtain ⟨hkC, hkP, hinj⟩ := hcentralCase hNc hNpg hNB
      exact ⟨hinj, thetaPlaneIntersection_map_eq_of_central_pKernel p hp π hsurj hkC hkP B hinj
        b hb hb1', fun c _ _ =>
          thetaCoreOf_element_centralizer_map_eq_of_central_pKernel p hp π hsurj hkC hkP c⟩
  obtain ⟨hinj, hT, hcore⟩ := key
  have hJ := thetaPlaneCommutators_map_eq_of_element_theta_images p π B hinj hcore
  refine ⟨?_, ?_, ?_, ?_, fun hNc hNpg hNB => ?_⟩
  · rw [card_map_eq_of_injOn π B hinj, hBcard]
  · rw [thetaT_eq_thetaPlaneIntersection hp, thetaT_eq_thetaPlaneIntersection hp]
    exact hT
  · rw [thetaJ_eq_thetaPlaneCommutators hp, thetaJ_eq_thetaPlaneCommutators hp]
    exact hJ
  · rw [thetaAlpha_eq_thetaPlaneAlpha hp, thetaAlpha_eq_thetaPlaneAlpha hp, thetaPlaneAlpha,
      thetaPlaneAlpha, Subgroup.map_sup, hJ, hT]
  · obtain ⟨hkC, hkP, hinj'⟩ := hcentralCase hNc hNpg hNB
    rw [thetaAlpha_eq_thetaPlaneAlpha hp, thetaAlpha_eq_thetaPlaneAlpha hp,
      aschbacherSolvableCore_eq_solvablePrimeComplementCore hp,
      aschbacherSolvableCore_eq_solvablePrimeComplementCore hp]
    exact thetaPlaneAlpha_le_theta_iff_of_central_pKernel p hp π hsurj hkC hkP B hB.1 hinj' b hb
      hb1'

end CFSG.RankThree.LocalRank
