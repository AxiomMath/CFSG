module

public import CFSG.RankThree.PartOne.S11d.PlaneAll
import CFSG.RankThree.SteinbergCBONOuterPrimes
import CFSG.RankThree.PartOne.KP.Co3Aut
import CFSG.Sporadic.Schreier.PairMcLOut
import CFSG.Sporadic.Schreier.J4SOuter
import CFSG.Sporadic.Schreier.RuAutInner
import CFSG.Sporadic.FischerOddCore.Fi23Aut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadicCases
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicBridgeB
public import CFSG.Sporadic.Schreier.M12

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def SporadicOutSmallAt (s : TauCeti.SporadicName) : Prop :=
  Nat.card (Outer (NativeSporadic.Carrier s)) < 25 ∨
    ∀ q : ℕ, q.Prime → 5 ≤ q → ¬ q ∣ Nat.card (Outer (NativeSporadic.Carrier s))

namespace OuterPrimeTwoBridge2

theorem sporadicOutSmallAt_M11
    : SporadicOutSmallAt .M11 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_m11_schreier.1 (by norm_num))

theorem sporadicOutSmallAt_M12
    : SporadicOutSmallAt .M12 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_m12_schreier.1 (by norm_num))

theorem sporadicOutSmallAt_M22
    : SporadicOutSmallAt .M22 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_m22_schreier.1 (by norm_num))

theorem sporadicOutSmallAt_M23
    : SporadicOutSmallAt .M23 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_m23_schreier.1 (by norm_num))

theorem sporadicOutSmallAt_M24
    : SporadicOutSmallAt .M24 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_m24_schreier.1 (by norm_num))

theorem sporadicOutSmallAt_J1
    : SporadicOutSmallAt .J1 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_j1_schreier.1.le (by norm_num))

theorem sporadicOutSmallAt_J2
    : SporadicOutSmallAt .J2 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.AT_J2_Schreier.1 (by norm_num))

theorem sporadicOutSmallAt_J3
    : SporadicOutSmallAt .J3 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.AT_J3_Schreier.1 (by norm_num))

theorem sporadicOutSmallAt_HS
    : SporadicOutSmallAt .HS :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.AT_HS_Schreier.1 (by norm_num))

theorem sporadicOutSmallAt_Suz
    : SporadicOutSmallAt .Suz :=
  Or.inl (lt_of_le_of_lt Sporadic.SuzOddCore.outer_carrier_suz.1.le (by norm_num))

theorem sporadicOutSmallAt_ONan
    : SporadicOutSmallAt .ONan :=
  Or.inr fun q hq hq5 hdvd => by
    rcases Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent q hq hdvd
      with rfl | rfl <;> omega

theorem sporadicOutSmallAt_Co3
    : SporadicOutSmallAt .Co3 :=
  Or.inl (lt_of_le_of_lt CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1.le (by norm_num))

theorem sporadicOutSmallAt_McL
    : SporadicOutSmallAt .McL :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.McL_outer_card_le_two.1 (by norm_num))

theorem sporadicOutSmallAt_He
    : SporadicOutSmallAt .He :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.AT_He_Schreier.1 (by norm_num))

theorem sporadicOutSmallAt_Fi22
    : SporadicOutSmallAt .Fi22 :=
  Or.inl (lt_of_le_of_lt
    (ComponentClassification.CatalogueOuterTwoPart.card_outer_fi22.le) (by norm_num))

theorem sporadicOutSmallAt_Fi23
    : SporadicOutSmallAt .Fi23 :=
  Or.inl (lt_of_le_of_lt Sporadic.FischerOddCore.card_outer_fi23.le (by norm_num))

theorem sporadicOutSmallAt_Fi24Prime
    : SporadicOutSmallAt .Fi24Prime :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.Fi24.card_outer_fi24prime.le (by norm_num))

theorem sporadicOutSmallAt_Ru
    : SporadicOutSmallAt .Ru := by
  refine Or.inl ?_
  rw [show Nat.card (Outer (NativeSporadic.Carrier .Ru)) =
      Nat.card (Outer Sporadic.RuSchreier.ruP) from
    OuterPrimeTwoBridge.card_outer_eq Sporadic.RuSchreier.ruEquivP,
    Sporadic.RuSchreier.card_outer_ruP]
  norm_num

theorem sporadicOutSmallAt_J4
    : SporadicOutSmallAt .J4 := by
  right
  intro q hq hq5 hdvd
  have hJ4 : Nonempty (NativeSporadic.Carrier .J4 ≃* NativeSporadic.J4) := ⟨MulEquiv.refl _⟩
  rcases (Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes
    (T := NativeSporadic.Carrier .J4) hJ4).1 q hq hdvd with rfl | rfl <;> omega

end OuterPrimeTwoBridge2

open OuterPrimeTwoBridge2 in
theorem sporadicOutSmall_of_simple
    (hopen : SporadicOuterOrderLeTwoSimple) : SporadicOutSmall := by
  have h7 : ∀ s, (s = .Co1 ∨ s = .Co2 ∨ s = .HN ∨ s = .Ly ∨ s = .Th ∨ s = .B ∨ s = .M) →
      ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
        Nonempty (T ≃* NativeSporadic.Carrier s) →
          Nat.card (Outer T) < 25 ∨ ∀ q : ℕ, q.Prime → 5 ≤ q → ¬ q ∣ Nat.card (Outer T) :=
    fun s hs T _ _ _ hnonab hT => Or.inl (lt_of_le_of_lt (hopen s hs T hnonab hT) (by norm_num))
  have hT : ∀ s, SporadicOutSmallAt s → ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T],
      (∃ a b : T, a * b ≠ b * a) → Nonempty (T ≃* NativeSporadic.Carrier s) →
        Nat.card (Outer T) < 25 ∨ ∀ q : ℕ, q.Prime → 5 ≤ q → ¬ q ∣ Nat.card (Outer T) := by
    intro s hs T _ _ _ _ ⟨e⟩
    have hcard : Nat.card (Outer T) = Nat.card (Outer (NativeSporadic.Carrier s)) :=
      Nat.card_congr (equivalence e).toEquiv
    rw [hcard]
    exact hs
  intro s
  cases s
  · exact hT _ sporadicOutSmallAt_M11
  · exact hT _ sporadicOutSmallAt_M12
  · exact hT _ sporadicOutSmallAt_M22
  · exact hT _ sporadicOutSmallAt_M23
  · exact hT _ sporadicOutSmallAt_M24
  · exact hT _ sporadicOutSmallAt_J1
  · exact hT _ sporadicOutSmallAt_J2
  · exact hT _ sporadicOutSmallAt_J3
  · exact hT _ sporadicOutSmallAt_J4
  · exact hT _ sporadicOutSmallAt_HS
  · exact hT _ sporadicOutSmallAt_McL
  · exact hT _ sporadicOutSmallAt_He
  · exact hT _ sporadicOutSmallAt_Ru
  · exact hT _ sporadicOutSmallAt_Suz
  · exact hT _ sporadicOutSmallAt_ONan
  · exact h7 .Co1 (by simp)
  · exact h7 .Co2 (by simp)
  · exact hT _ sporadicOutSmallAt_Co3
  · exact hT _ sporadicOutSmallAt_Fi22
  · exact hT _ sporadicOutSmallAt_Fi23
  · exact hT _ sporadicOutSmallAt_Fi24Prime
  · exact h7 .HN (by simp)
  · exact h7 .Ly (by simp)
  · exact h7 .Th (by simp)
  · exact h7 .B (by simp)
  · exact h7 .M (by simp)

end CFSG.RankThree.PartOne
