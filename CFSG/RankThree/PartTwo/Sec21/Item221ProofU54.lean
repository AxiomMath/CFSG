module

public import CFSG.RankThree.PartTwo.Sec21.Item221ProofStatements
public import CFSG.RankThree.CentralLift.EvenCenterTrivial
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.PartTwo.Sec21.Item22Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU localRank)

theorem su54LocalRankFive :
    SU54LocalRankFive := by
  intro Q _ _ hQ h5 ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect Q := hQ
  by_contra hlt
  have hloc : localRank 5 Q ≤ 2 := by omega
  have : IsSimpleGroup (projSU 5 2 2) := isSimpleGroup_projSU (by norm_num) (by norm_num)
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := e.isSimpleGroup
  have hnab : ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hp : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    exact not_subsingleton _
      (subsingleton_of_isPerfect_of_isSolvable hp (Group.isSolvable_of_comm h))
  have hq : CFSG.IsQuasisimple Q := ⟨hQ, hs, hnab⟩
  have hZ5 : IsPGroup 5 (Subgroup.center Q) := IsPGroup.of_card (n := 1) (by rw [h5]; norm_num)
  have hM := CFSG.SectionRank.statedClassicalModel_of_mulEquiv e
    (statedClassicalModel_projSU (m := 5) (b := 2) (by norm_num) (by norm_num))
  have hZ := CFSG.RankThree.CentralLift.even_unitary_small_local_rank_prime_center_trivial
    (by norm_num : Nat.Prime 5) (by norm_num) hq hZ5 hloc hM
  rw [hZ, Subgroup.card_bot] at h5
  omega

end CFSG.RankThree.PartTwo.Sec21
