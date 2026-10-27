module

public import CFSG.RankThree.PartTwo.KFacts.KS21Terminal
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (GLBStronglyEmbedded)
open CFSG.Assembly (IsElemAbelian)

@[expose] def GL83StronglyEmbeddedThreeSolvable : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsKGroup X → ∀ M : Subgroup X,
    GLBStronglyEmbedded 3 M → 2 ≤ CFSG.Open.pRank 3 M →
      ∀ (H : Subgroup X) (T : Subgroup H) [T.Normal], H ≤ M → IsSimpleGroup (H ⧸ T) →
        Nat.card (H ⧸ T) = 3 ∨ Nat.Coprime 3 (Nat.card (H ⧸ T))

@[expose] def AS76InvolutionsCentralizeThree : Prop :=
  ∀ (X : Type) [Group X], KFacts.KS21.IsTerminalGroup X →
    ∀ φ : MulAut X, orderOf φ = 2 → ∃ y : X, orderOf y = 3 ∧ φ y = y

variable {G : Type} [Group G]

theorem pRank_le_pRank_subgroupOf [Finite G] {p : ℕ} (hp : p.Prime) {K C : Subgroup G}
    (hKC : K ≤ C) : CFSG.Open.pRank p K ≤ CFSG.Open.pRank p (K.subgroupOf C) := by
  obtain ⟨E, hEK, hEe, hEc⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained p hp K
  apply le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove p hp _)
  have hEe' := isElemAbelian_subgroupOf (p := p) (E := E) ⟨hEe.1, hEe.2⟩ C
  refine ⟨E.subgroupOf C, fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hEK (Subgroup.mem_subgroupOf.mp hx)), ⟨hEe'.1, hEe'.2⟩, ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEK.trans hKC)).toEquiv]
  exact hEc

theorem pRank_pos_of_orderOf_eq_three [Finite G] {K : Subgroup G} {y : G} (hy : orderOf y = 3)
    (hyK : y ∈ K) : 0 < CFSG.Open.pRank 3 K := by
  have hE : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers y) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      simp only [Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hy,
        pow_orderOf_eq_one, one_zpow]
  have h1 : 1 ≤ CFSG.Open.pRank 3 K := by
    apply le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three K)
    exact ⟨_, (Subgroup.zpowers_le).mpr hyK, hE, by rw [Nat.card_zpowers, hy, pow_one]⟩
  omega

end CFSG.RankThree.PartTwo.Sec21
