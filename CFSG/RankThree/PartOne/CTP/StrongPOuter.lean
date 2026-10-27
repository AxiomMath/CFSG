module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadic
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.Sporadic.Schreier.M24
import CFSG.Sporadic.SuzOddCore.Outer
import CFSG.Sporadic.Schreier.J4SOuter
import CFSG.RankThree.SteinbergCBONOuterPrimes
import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.Blueprint TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

@[expose] def SporadicOuterNoLargePrime : Prop :=
  ∀ s ∈ Census3.sporadicsThm3, ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T],
    (∃ a b : T, a * b ≠ b * a) → Nonempty (T ≃* NativeSporadic.Carrier s) →
      ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (Outer T)

theorem sporadicOuterNoLargePrime_of_leTwo
    (hLeTwo : SporadicOuterOrderLeTwoSimple) : SporadicOuterNoLargePrime := by
  intro s hs T _ _ _ hnc ⟨e⟩ p hp hp5 hdvd
  have hcard : Nat.card (Outer T) = Nat.card (Outer (NativeSporadic.Carrier s)) :=
    Nat.card_congr (equivalence e).toEquiv
  have hMA : Finite (MulAut T) :=
    Finite.of_injective (fun σ : MulAut T => (σ : T → T)) DFunLike.coe_injective
  have hfin : Finite (Outer T) := inferInstance
  have hpos : 0 < Nat.card (Outer T) := Nat.card_pos
  have hs' : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J3 ∨
      s = .J4 ∨ s = .McL ∨ s = .Ly ∨ s = .HS ∨ s = .He ∨ s = .Suz ∨ s = .Ru ∨ s = .ONan ∨
      s = .Co3 ∨ s = .Co2 ∨ s = .HN ∨ s = .Th := by
    simpa [Census3.sporadicsThm3] using hs
  have le2 : ∀ {t : SporadicName}, (t = .M11 ∨ t = .M12 ∨ t = .M23 ∨ t = .J1 ∨ t = .J2 ∨ t = .J3 ∨
      t = .McL ∨ t = .HS ∨ t = .He ∨ t = .Ru) → Nat.card (Outer (NativeSporadic.Carrier t)) ≤ 4 :=
    fun ht => (PartTwo.Sec4.card_outer_carrier_le_two ht).trans (by norm_num)
  have key : Nat.card (Outer T) ≤ 4 ∨
      ∀ q : ℕ, q.Prime → q ∣ Nat.card (Outer T) → q = 2 ∨ q = 3 := by
    rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; rw [hcard]; exact le2 (by simp)
    · left; rw [hcard]; exact le2 (by simp)
    · left; rw [hcard]; exact Sporadic.Schreier.at_m22_schreier.1
    · left; rw [hcard]; exact le2 (by simp)
    · left; rw [hcard]; exact Sporadic.Schreier.at_m24_schreier.1
    · left; rw [hcard]; exact le2 (by simp)
    · left; rw [hcard]; exact le2 (by simp)
    · left; rw [hcard]; exact le2 (by simp)
    · right
      intro q hq hqd
      rw [hcard] at hqd
      have hJ4 : Nonempty (NativeSporadic.Carrier .J4 ≃* NativeSporadic.J4) := ⟨MulEquiv.refl _⟩
      exact (Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes
        (T := NativeSporadic.Carrier .J4) hJ4).1 q hq hqd
    · left; rw [hcard]; exact le2 (by simp)
    · exact Or.inl ((hLeTwo .Ly (by simp) T hnc ⟨e⟩).trans (by norm_num))
    · left; rw [hcard]; exact le2 (by simp)
    · left; rw [hcard]; exact le2 (by simp)
    · left; rw [hcard]; exact Sporadic.SuzOddCore.outer_carrier_suz.1.le.trans (by norm_num)
    · left; rw [hcard]; exact le2 (by simp)
    · right
      intro q hq hqd
      rw [hcard] at hqd
      exact Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent q hq hqd
    · left; rw [hcard]
      exact CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1.le.trans (by norm_num)
    · exact Or.inl ((hLeTwo .Co2 (by simp) T hnc ⟨e⟩).trans (by norm_num))
    · exact Or.inl ((hLeTwo .HN (by simp) T hnc ⟨e⟩).trans (by norm_num))
    · exact Or.inl ((hLeTwo .Th (by simp) T hnc ⟨e⟩).trans (by norm_num))
  rcases key with h4 | hno
  · have := Nat.le_of_dvd hpos hdvd
    omega
  · rcases hno p hp hdvd with rfl | rfl <;> omega

end CFSG.RankThree.PartOne.CTP
