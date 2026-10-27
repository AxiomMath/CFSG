module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallCF


public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {P : ∀ (X : Type) [Group X], Prop}

theorem sectionalTwoRankLE_one_of_not_four_dvd {X : Type*} [Group X] [Finite X]
    (h : ¬ 4 ∣ Nat.card X) : CFSG.GH74.SectionalTwoRankLE X 1 := by
  intro S hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hdvd : 2 ^ n ∣ Nat.card X := hn ▸ Subgroup.card_subgroup_dvd_card S
  have hn1 : n ≤ 1 := by
    by_contra hn1
    exact h (by simpa using (pow_dvd_pow 2 (show 2 ≤ n by omega)).trans hdvd)
  have hS2 : Nat.card S ∣ 2 := by
    rw [hn]
    exact (pow_dvd_pow 2 hn1).trans (pow_one 2).dvd
  have : IsCyclic S := isCyclic_of_card_dvd_prime hS2
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic S)
  refine ⟨{(g : X)}, by simp, ?_⟩
  have h' := congrArg (Subgroup.map S.subtype) hg
  rw [MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype] at h'
  rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]
  exact h'

theorem not_isCompositionFactor_of_isSolvable_normal
    (hP : ∀ (L : Type) [Group L] [Finite L], P L →
      (∃ a b : L, a * b ≠ b * a) ∧ ¬ CFSG.GH74.SectionalTwoRankLE L 2)
    {X : Type} [Group X] [Finite X] (S : Subgroup X) [S.Normal] (hS : Group.IsSolvable S)
    (hi : ¬ 4 ∣ S.index) (L : Type) [Group L] (h : E1.IsCompositionFactor X L) : ¬ P L := by
  refine not_isCompositionFactor_of_normal S ?_ ?_ L h
  · exact not_isCompositionFactor_of_isSolvable (fun L _ _ hL => (hP L hL).1) hS
  · refine not_isCompositionFactor_of_sectionalTwoRankLE (fun L _ _ hL => (hP L hL).2)
      (CFSG.GH74.SectionalTwoRankLE.mono (by norm_num)
        (sectionalTwoRankLE_one_of_not_four_dvd ?_))
    rwa [← Subgroup.index_eq_card]

theorem not_hasCompFactor_normalizer_of_relIndex_two
    (hP : ∀ (L : Type) [Group L] [Finite L], P L →
      (∃ a b : L, a * b ≠ b * a) ∧ ¬ CFSG.GH74.SectionalTwoRankLE L 2)
    {Q : Type} [Group Q] [Finite Q] {E T A : Subgroup Q} [E.Normal] (hq : Group.IsSolvable (Q ⧸ E))
    (hT : IsSylowIn 2 (T ⊓ E) E) (hAT : A ≤ T ⊓ E) (hA : IsMulCommutative ↥A)
    (hAi : A.relIndex (T ⊓ E) = 2) :
    ¬ HasCompFactor (Subgroup.normalizer (A : Set Q)) P := by
  set N := Subgroup.normalizer (A : Set Q)
  refine not_hasCompFactor_of_subgroupOf (fun L _ _ hL => (hP L hL).1) hq N ?_
  have hle : A ≤ E ⊓ N := le_inf (hAT.trans inf_le_right) Subgroup.le_normalizer
  have hTN : T ⊓ E ≤ N :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAT).1 (Subgroup.normal_of_index_eq_two hAi)
  have hTle : T ⊓ E ≤ E ⊓ N := le_inf inf_le_right hTN
  have : (A.subgroupOf (E ⊓ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 inf_le_right
  have := hA
  refine not_isCompositionFactor_of_mulEquiv
    ((MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right E N).symm).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_right)).symm
    (not_isCompositionFactor_of_isSolvable_normal hP (A.subgroupOf (E ⊓ N))
      (solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hle).symm.surjective) ?_)
  have h1 := Subgroup.relIndex_mul_relIndex A (T ⊓ E) (E ⊓ N) hAT hTle
  have h2 := Subgroup.relIndex_mul_relIndex (T ⊓ E) (E ⊓ N) E hTle inf_le_left
  have hodd := hT.2.2
  rw [hAi] at h1
  change ¬ 4 ∣ A.relIndex (E ⊓ N)
  rw [← h1]
  intro h4
  apply hodd
  rw [← h2]
  exact Dvd.dvd.mul_right (by omega) _

end CFSG.LocalAnalysis.WeakClosure81

end
