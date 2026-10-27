module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountSupport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinBaseCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseTotalInvolutionCount
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
The base counting package plus finite-support reduction gives the source
identities (1)--(4).  The restriction and pair-counting arguments are kept
out of this module; this theorem is the arithmetic/interface boundary they
consume.
-/

public theorem firstCase_klein_count_equations_one_to_four
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (hvanish : ∀ n : ℕ, 5 ≤ n → cosetInvolution_b c.Hhat n = 0) :
    ∃ K : Subgroup G, ∃ b0 b1 b2 b3 b4 : ℕ,
      IsHallIn K c.FU ∧ K ≠ ⊥ ∧
      (∀ n : ℕ, n ≤ 4 →
        Nat.card {x : G // x ∈ firstCaseJ c n} =
          n * firstCaseBn b0 b1 b2 b3 b4 n) ∧
      Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} = 3 + 2 * Nat.card K ∧
      Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat} = 3 + 6 * Nat.card K ∧
      c.H.index = 3 * c.Hhat.index ∧
      Nat.card {x : G // IsInvolution x} =
        3 + 6 * Nat.card K + b1 + 2 * b2 + 3 * b3 + 4 * b4 ∧
      c.Hhat.index = 1 + b0 + b1 + b2 + b3 + b4 ∧
      6 * Nat.card K + b4 = 3 * b0 + 2 * b1 + b2 := by
  obtain ⟨K, hKHall, hKne, hHcount, hHhatcount, hindex⟩ :=
    firstCase_klein_base_count_package hmin c hfirst hklein
  have hKcardge : 2 ≤ Nat.card K := by
    have hKcardpos : 0 < Nat.card K := Nat.card_pos
    have hKcardne : Nat.card K ≠ 1 := by
      intro hcard
      apply hKne
      exact Subgroup.eq_bot_of_card_eq K hcard
    omega
  have hJhat_le : Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat} ≤
      Nat.card {x : G // IsInvolution x} := by
    exact Nat.card_le_card_of_injective
      (fun x => (⟨x.1, x.2.1⟩ : {x : G // IsInvolution x}))
      (by
        intro x y h
        apply Subtype.ext
        exact congrArg
          (fun z : {x : G // IsInvolution x} => (z : G)) h)
  have hJge : 4 ≤ Nat.card {x : G // IsInvolution x} := by
    have hJhat : 15 ≤ Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat} := by
      rw [hHhatcount]
      omega
    omega
  obtain ⟨b0, b1, b2, b3, b4, hJn, hsum, htotal⟩ :=
    firstCase_count_support_five c hvanish hJge
  have htotal' : Nat.card {x : G // IsInvolution x} =
      3 + 6 * Nat.card K + b1 + 2 * b2 + 3 * b3 + 4 * b4 := by
    rw [htotal, hHhatcount]
    omega
  have htotalIndex := firstCase_total_involution_card_eq_H_index hmin c
  have h4 : 6 * Nat.card K + b4 = 3 * b0 + 2 * b1 + b2 := by
    rw [htotalIndex, hindex, hsum] at htotal'
    omega
  exact ⟨K, b0, b1, b2, b3, b4, hKHall, hKne, hJn, hHcount,
    hHhatcount, hindex, htotal', hsum, h4⟩

end CFSG.GorensteinWalter
