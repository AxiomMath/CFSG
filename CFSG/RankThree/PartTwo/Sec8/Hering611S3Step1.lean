module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SK1
import CFSG.RankThree.PartTwo.Sec12.Item125Act

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section Step1


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem step1_general (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    (hin : ∀ γ : MulAut (K ⧸ aschbacherSolvableCore 3 K), γ ^ 3 = 1 → KFacts.IsInnerAut γ) :
    ∃ (k : K) (j : ℤ), (k : G) ∈ A ∧ c = d ^ j * (k : G) ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) k ≠ 1 ∧
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) ^ 3 = 1 ∧
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) =
        thetaQuotMulAut K (compAction K ⟨c, C.A_le_normalizer_K h45 C.c_mem⟩) := by
  have hAe := C.toFrame611.isElemAbelian
  obtain ⟨k, hkA, hck, hkact⟩ := exists_mul_mem_zpowers_d h45 C hZ hin C.c_mem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hck
  have hk1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) k ≠ 1 := by
    intro h1
    apply C.c_not_cent
    rw [Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct (C.A_le_normalizer_K h45 C.c_mem)]
    have h2 : thetaQuotMulAut K (compAction K ⟨c, C.A_le_normalizer_K h45 C.c_mem⟩) = 1 := by
      rw [← hkact, h1, map_one]
    exact h2
  have hk3 : (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) ^ 3 = 1 := by
    have h3 : k ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 (k : G) hkA)
    rw [← map_pow, h3, map_one]
  refine ⟨k, j, hkA, ?_, hk1, hk3, hkact⟩
  rw [hj]
  group

end Step1

end CFSG.RankThree.PartTwo.Sec8.Hering611
