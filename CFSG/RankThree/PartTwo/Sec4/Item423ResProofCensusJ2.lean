module

public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofCensus
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem census423_of_j2 (h415 : Item4_15) {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) : Census423 X := by
  intro D hD hD9 Y _ _
  right
  right
  refine ⟨Or.inr hX, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hDP⟩ := (Sec5.isPGroup_of_isElemAbelian hD.prop).exists_le_sylow
  obtain ⟨-, -, -, h4, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨hZ3, -, -⟩ := Sec14.j2_sylow_facts h415 hX P
  obtain ⟨a, haD, haZ⟩ : ∃ a ∈ D,
      a ∉ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) :=
      fun a ha => hcon a ha
    have h1 := Subgroup.card_le_of_le hle
    rw [hD9, hZ3] at h1
    norm_num at h1
  exact (h4 D ⟨hDP, hD9⟩ a haD haZ).1

@[expose] def K423Inner46FiveRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Five X →
    ¬ Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

theorem k423Inner46Five_of (h415 : Item4_15) (h : K423Inner46FiveRest) : K423Inner46Five := by
  intro X _ _ hX hq hZ hSL
  by_cases hJ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)
  · exact census423_of_j2 h415 hJ
  · exact h X hX hJ hq hZ hSL

theorem k423InnerCensus_of_rest'
    (h1 : K423Inner46OneThree) (h3 : K423Inner46Three) (h4 : K423Inner46Four)
    (h5 : K423Inner46FiveRest) (h6 : K423Inner46SixRest) (h7 : K423Inner46Seven)
    (h8 : K423Inner46Eight) : K423InnerCensus :=
  k423InnerCensus_of (k423Inner46One_of h1) k423Inner46Two h3 h4
    (k423Inner46Five_of Sporadic.rank3II_4_15 h5) (k423Inner46Six_of h6) h7 h8

end CFSG.RankThree.PartTwo.Sec4
