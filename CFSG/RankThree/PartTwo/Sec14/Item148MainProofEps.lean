module

import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type} [Group G] [Finite G]

namespace Main148

theorem eq_top_or_le_center_of_isSubnormal {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    {P : Subgroup Q} (hP : P.IsSubnormal) : P = ⊤ ∨ P ≤ Subgroup.center Q := by
  induction hP with
  | top => exact Or.inl rfl
  | step H K hHK _ hN ih =>
    rcases ih with rfl | hK
    · have hHn : H.Normal := Subgroup.normalizer_eq_top_iff.mp
        (top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hN))
      exact CFSG.LocalCores.quasisimple_normal_subgroups hQ hHn
    · exact Or.inr (hHK.trans hK)

theorem eq_of_le_of_isSubnormal_of_isQuasisimple {Γ : Type*} [Group Γ] {K J : Subgroup Γ}
    (hKJ : K ≤ J) (hJ : IsQuasisimple ↥J) (hKp : Group.IsPerfect ↥K) (hK1 : Nontrivial ↥K)
    (hKs : (K.subgroupOf J).IsSubnormal) : K = J := by
  rcases eq_top_or_le_center_of_isSubnormal hJ hKs with htop | hcen
  · exact le_antisymm hKJ (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    have hcomm : ∀ a b : ↥K, a * b = b * a := by
      intro a b
      have ha : (⟨a, hKJ a.2⟩ : ↥J) ∈ Subgroup.center ↥J := hcen a.2
      have h := Subgroup.mem_center_iff.mp ha ⟨b, hKJ b.2⟩
      exact Subtype.ext (congrArg Subtype.val h).symm
    exact Group.IsPerfect.not_isSolvable ↥K (Group.isSolvable_of_comm hcomm)

theorem isSimpleGroup_of_eps {X : Type} [Group X] (hXp : Group.IsPerfect X) {p f : ℕ}
    [Fact p.Prime] (hf : 1 ≤ f)
    (h : (p ^ f % 3 = 2 ∧ Nonempty (X ≃* projSL 3 (GaloisField p f))) ∨
      (p ^ f % 3 = 1 ∧ 2 < p ^ f ∧ Nonempty (X ≃* projSU 3 p f))) :
    IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ 3 ∣ Nat.card X := by
  have hs : IsSimpleGroup X ∧ 3 ∣ Nat.card X := by
    rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, hq, ⟨φ⟩⟩
    · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField p f)
      exact ⟨MulEquiv.isSimpleGroup φ, KFacts.three_dvd_card_of_mulEquiv_projSL φ⟩
    · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf (by omega)
      exact ⟨MulEquiv.isSimpleGroup φ, KFacts.three_dvd_card_of_mulEquiv_projSU (by omega) φ⟩
  have : Nontrivial X := hs.1.toNontrivial
  exact ⟨hs.1, exists_ne_comm_of_isPerfect hXp, hs.2⟩

end Main148

open Main148

end CFSG.RankThree.PartTwo.Sec14
