module

public import CFSG.RankThree.PartTwo.Sec18.Item189KTypeBridge
import CFSG.RankThree.PartTwo.Sec18.Item189KType

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late

theorem pRank_three_top_quotient_theta {X : Type} [Group X] [Finite X] :
    CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ aschbacherSolvableCore 3 X)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, -, hndvd, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hk : Nat.Coprime 3 (Nat.card (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hndvd
  exact (CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3 Nat.prime_three
    (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) (QuotientGroup.mk'_surjective _) hk).symm

section Certified


theorem step189KType
    : Step189KType := by
  intro G _ _ A M H c hH _ hK hr
  set K := normalClosureIn M c
  have hsimple : IsSimpleGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K) := ktype_simple hK hr
  have hnab : ∃ a b : ↥K ⧸ aschbacherSolvableCore 3 ↥K, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := quasisimple_of_mem_thetaComponentsIn hK
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a, b, fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ aschbacherSolvableCore 3 ↥K)) = 1 :=
    pRank_three_top_quotient_theta.trans
      ((CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num)
        K).symm.trans hr)
  have : IsSimpleGroup G := hH.isSimpleGroup
  have hMtop : M ≠ ⊤ :=
    ne_top_of_pCoreOf_ne_bot hH.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal hH.mem_scriptM.1)
  have hKtop : K ≠ ⊤ := ne_top_of_le_ne_top hMtop (mem_thetaComponentsIn_iff.mp hK).1
  have hKG : IsKGroup ↥K := (hH.toTheoremFourHyp.sectionFourHyp hKtop).kGroup
  obtain ⟨i, ⟨e⟩⟩ : Assembly.InCatalog (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    KCore.KGroupAllSimple.catalogue_self (C := Assembly.InCatalog)
      Assembly.inCatalog_isoInvariant (hKG.quotient _)
  exact isRankOneType189_of_index hsimple hnab i e h3

end Certified

end CFSG.RankThree.PartTwo.Sec18
