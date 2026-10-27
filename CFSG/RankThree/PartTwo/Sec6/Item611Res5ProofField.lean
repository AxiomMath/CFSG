module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofField
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)


section Certs


@[expose] def Item611FieldL2Max : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      (∃ e ∈ A, ∃ m : ℕ, 2 < m ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
        KFacts.InducesStdKind L e .field) →
      c ∈ E → ∀ d ∈ E ⊓ Subgroup.centralizer (T : Set G), d ∉ Subgroup.zpowers c →
      ∀ S ∈ invariantPiSubgroups (Subgroup.centralizer {d} ⊓ Subgroup.centralizer (T : Set G)) E
          (piOf 2),
        S ≠ ⊥ → ⁅S, Subgroup.zpowers c⁆ = S →
        T ∈ maxInvariantPiSubgroups (Subgroup.centralizer {d}) E (piOf 2)

end Certs

namespace Res611Res5

variable {G : Type} [Group G] [Finite G]

theorem false_of_mem_maxInvariantPiSubgroups {E T S : Subgroup G} {c d : G}
    (hmax : T ∈ maxInvariantPiSubgroups (Subgroup.centralizer {d}) E (piOf 2))
    (hcT : c ∈ Subgroup.centralizer (T : Set G))
    (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer {d} ⊓ Subgroup.centralizer (T : Set G))
      E (piOf 2)) (hS1 : S ≠ ⊥) (hSc : ⁅S, Subgroup.zpowers c⁆ = S) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := hmax.1
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hS hT
  obtain ⟨hSle, hS2, hES⟩ := hS
  obtain ⟨hTd, hT2, hET⟩ := hT
  have hTS : T ≤ Subgroup.normalizer (S : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun s hs =>
      (Subgroup.mem_centralizer_iff.mp ((hSle hs).2) x hx).symm)
  have hY : T ⊔ S ∈ invariantPiSubgroups (Subgroup.centralizer {d}) E (piOf 2) := by
    rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
    exact ⟨sup_le hTd fun x hx => (hSle hx).1, hT2.to_sup_of_normal_right' hS2 hTS,
      fun x hx => Subgroup.inf_normalizer_le_normalizer_sup T S ⟨hET hx, hES hx⟩⟩
  have hST : S ≤ T := le_sup_right.trans (hmax.2 hY le_sup_left)
  have hTc : ⁅T, Subgroup.zpowers c⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
      Subgroup.zpowers_le]
    exact hcT
  apply hS1
  rw [← hSc, eq_bot_iff, ← hTc]
  exact Subgroup.commutator_mono hST le_rfl

end Res611Res5

open Res611Res5

section Certs


theorem item611FieldL2S_of_max (hM : Item611FieldL2Max) : Item611FieldL2S := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he hcE d hd hdc S hS hS1
    hSc
  have hcT : c ∈ Subgroup.centralizer (T : Set G) := by
    have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
      le_centralizer_of_mem_thetaComponentsAt hL.1
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (hTL ht))
  exact false_of_mem_maxInvariantPiSubgroups
    (hM G hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he hcE d hd hdc S hS hS1 hSc)
    hcT hS hS1 hSc

end Certs

end CFSG.RankThree.PartTwo.Sec6
