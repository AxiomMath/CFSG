module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207RankTwo
import CFSG.Milestones.ASVolI.F45.Sp4
import CFSG.Milestones.ASVolI.F45.U

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ASVolI

private theorem uc22sp207_noStrongParabolic_of_system {X : Type} [Group X] [Finite X]
    (D : CFSG.GH74.BNPair.RankTwoSystem X 4) (hD : ChF.IsSylowOf 2 D.U ⊤) :
    NoStrongParabolic X :=
  uc22sp207_noStrongParabolic_of_rankTwo D (by decide) hD.2.1
    (Subgroup.relIndex_top_right D.U ▸ hD.2.2)

theorem uc22sp207_noStrongParabolic_Sp4 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsSp4 X n) : NoStrongParabolic X := by
  rcases h with ⟨-, ⟨-, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn hK
    have : Finite (StatedProj (StatedSp 2 K)) := Finite.of_equiv X e.toEquiv
    exact (uc22sp207_noStrongParabolic_of_system (burnsideF45_sp4System K)
      (burnsideF45_sp4System_isSylow K Nat.prime_two)).of_mulEquiv e.symm
  all_goals exact absurd h0 (by decide)

theorem uc22sp207_noStrongParabolic_U4 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsU4 X n) : NoStrongParabolic X := by
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hK
    obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hK
    have : Fact ((ζ : K) ≠ 0) := ⟨hζ⟩
    have : Finite (StatedProj (StatedSU 4 (2 ^ n) K)) := Finite.of_equiv X e.toEquiv
    exact (uc22sp207_noStrongParabolic_of_system (burnsideF45U4_system hK ζ)
      (burnsideF45U4_system_isSylow hK ζ)).of_mulEquiv e.symm
  all_goals exact absurd h0 (by decide)

theorem uc22sp207_noStrongParabolic_U5 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsU5 X n) : NoStrongParabolic X := by
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hK
    obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hK
    have : Fact ((ζ : K) ≠ 0) := ⟨hζ⟩
    have : Finite (StatedProj (StatedSU 5 (2 ^ n) K)) := Finite.of_equiv X e.toEquiv
    exact (uc22sp207_noStrongParabolic_of_system (burnsideF45U5_system hK ζ)
      (burnsideF45U5_system_isSylow hK ζ)).of_mulEquiv e.symm
  all_goals exact absurd h0 (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UC22
