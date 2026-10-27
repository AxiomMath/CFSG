module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofAfter
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofLift

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof


@[expose] def KF83KBarEven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (A₀ : Subgroup G) (d : G) (n : ℕ), Hyp81 G A c L a → 27 < Nat.card A →
      Data83 G c L a A₀ d n →
        2 ∣ Nat.card (imageModTheta L (inSubgroup perfectResidual
          (L ⊓ Subgroup.centralizer {d})) ⊓ barCentralizer (Subgroup.zpowers a) L : Subgroup _)

theorem kF83KBarTwo_of_even (h : KF83KBarEven) : KF83KBarTwo := by
  intro G _ _ A c L a A₀ d n h81 hA hd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ⊓
    barCentralizer (Subgroup.zpowers a) L with hH
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 (h G A c L a A₀ d n h81 hA hd)
  have ht' : orderOf (t : L ⧸ aschbacherSolvableCore 3 L) = 2 := by
    rw [← ht]
    exact orderOf_submonoid t
  refine ⟨Subgroup.zpowers (t : L ⧸ aschbacherSolvableCore 3 L), ?_, ?_, ?_, ?_⟩
  · intro h1
    have h2 : (t : L ⧸ aschbacherSolvableCore 3 L) = 1 := by
      rw [← Subgroup.mem_bot, ← h1]
      exact Subgroup.mem_zpowers _
    rw [h2, orderOf_one] at ht'
    omega
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
  · rw [Subgroup.zpowers_le]
    exact t.2.1
  · rintro τ hτ _ ⟨k, rfl⟩
    have hfix : τ (t : L ⧸ aschbacherSolvableCore 3 L) = t := by
      have h1 := (FixedPoints.mem_subgroup _ _ _).mp t.2.2 ⟨τ, hτ⟩
      exact h1
    change τ ((t : L ⧸ aschbacherSolvableCore 3 L) ^ k) ∈ _
    rw [map_zpow, hfix]
    exact Subgroup.zpow_mem_zpowers _ k

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
