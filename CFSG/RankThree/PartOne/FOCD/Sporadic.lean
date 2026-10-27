module

public import CFSG.RankThree.PartOne.FOCD.OrdLemma
public import CFSG.RankThree.PartOne.FOCD.PpdLemma
public import CFSG.RankThree.PartOne.FOCD.CycSylow
public import CFSG.RankThree.PartOne.FOCD.LyFive
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
import CFSG.Sporadic.Schreier.J4SOuter
import CFSG.RankThree.SteinbergCBONOuterPrimes

public section

namespace CFSG.RankThree.PartOne.FOCD

open CFSG CFSG.Blueprint CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.RankThree.PartOne.Census3 (sporadicsThm3)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

open CFSG.Timmesfeld
open TauCeti (SporadicName)


theorem sporadic_order_facts
    {s : SporadicName} (hs : s ∈ sporadicsThm3) :
    Nat.card (NativeSporadic.Carrier s) ∣ N71 ∧
      (31 ∣ Nat.card (NativeSporadic.Carrier s) → s = .J4 ∨ s = .ONan ∨ s = .Th ∨ s = .Ly) := by
  simp only [sporadicsThm3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show Nat.card (NativeSporadic.Carrier .M11) = _ from CFSG.Sporadic.Mathieu.card_M11]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .M12) = _ from CFSG.Sporadic.Mathieu.card_M12]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .M22) = _ from CFSG.Sporadic.Mathieu.card_M22]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .M23) = _ from CTP.card_M23]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .M24) = _ from CFSG.Sporadic.Mathieu.card_M24]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .J1) = _ from CFSG.Sporadic.J1.card_J1]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .J2) = _ from CFSG.Sporadic.J2.card_J2]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .J3) = _ from CFSG.Sporadic.J3.card_J3]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .J4) = _ from CFSG.Sporadic.J4.card_J4]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun _ => Or.inl rfl⟩
  · rw [show Nat.card (NativeSporadic.Carrier .McL) = _ from CFSG.Sporadic.McL.card_McL]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .Ly) = _ from CFSG.Sporadic.Ly.card_Ly]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun _ => Or.inr (Or.inr (Or.inr rfl))⟩
  · rw [show Nat.card (NativeSporadic.Carrier .HS) = _ from CFSG.Sporadic.HS.card_HS]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .He) = _ from CFSG.Sporadic.He.card_He]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .Suz) = _ from CFSG.Sporadic.Suz.card_Suz]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .Ru) = _ from CFSG.Sporadic.Ru.card_Ru]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .ONan) = _ from CFSG.Sporadic.ON.card_ON_eq]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun _ => Or.inr (Or.inl rfl)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .Co3) = _ from CFSG.Sporadic.Co3.card_Co3]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .Co2) = _ from CFSG.Sporadic.Co2.card_Co2]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .HN) = _ from CFSG.Sporadic.HN.card_HN]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun h => absurd h (by decide +kernel)⟩
  · rw [show Nat.card (NativeSporadic.Carrier .Th) = _ from CTP.card_Th]
    exact ⟨Nat.dvd_of_mod_eq_zero (by decide +kernel), fun _ => Or.inr (Or.inr (Or.inl rfl))⟩

theorem not_ppd_of_small_prime {r j : ℕ} (hr : r ∈ ({2, 3, 5, 7, 13, 19, 31} : Finset ℕ))
    (hj : 10 ≤ j) (hj10 : 10 ∣ j) : ¬ IsPrimitivePrimeDivisor r j := by
  rintro ⟨-, hdvd, hprim⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  · exact hprim 2 (by norm_num) (by omega) (by norm_num)
  · exact hprim 4 (by norm_num) (by omega) (by norm_num)
  · exact hprim 3 (by norm_num) (by omega) (by norm_num)
  · by_cases h10 : j = 10
    · subst h10; norm_num at hdvd
    · exact hprim 12 (by norm_num) (by omega) (by norm_num)
  · by_cases h10 : j = 10
    · subst h10; norm_num at hdvd
    · exact hprim 18 (by norm_num) (by omega) (by norm_num)
  · exact hprim 5 (by norm_num) (by omega) (by norm_num)

theorem mem_primes_Th {r : ℕ} (hr : r.Prime) (h : r ∣ 90745943887872000) :
    r ∈ ({2, 3, 5, 7, 13, 19, 31} : Finset ℕ) := by
  have h1 : r ∈ Nat.primeFactors 90745943887872000 :=
    Nat.mem_primeFactors.2 ⟨hr, h, by norm_num⟩
  have h2 : Nat.primeFactors 90745943887872000 = {2, 3, 5, 7, 13, 19, 31} := by
    norm_num [Nat.primeFactors]
  rwa [h2] at h1

section Th


theorem fieldInnerT_Th_five {T : Type} [Group T] [Finite T]
    (hcard : Nat.card T = 90745943887872000) : FieldInnerT 5 T := by
  refine fieldInnerT_of_no_ppd (by norm_num) fun f hf r hr hdvd => ?_
  have hmem := mem_primes_Th hr (hcard ▸ hdvd)
  exact ⟨not_ppd_of_small_prime hmem (by omega) ⟨f, by ring⟩,
    not_ppd_of_small_prime hmem (by omega) ⟨2 * f, by ring⟩⟩

end Th

section Main


theorem fieldInnerSpor : FieldInnerSpor := by
  intro s hs T _ _ p hp hp5 hsimple hnab ⟨e⟩
  have hcard : Nat.card T = Nat.card (NativeSporadic.Carrier s) := Nat.card_congr e.toEquiv
  obtain ⟨hN71, h31⟩ := sporadic_order_facts hs
  by_cases h5 : p = 5 ∧ 31 ∣ Nat.card (NativeSporadic.Carrier s)
  · obtain ⟨rfl, h31'⟩ := h5
    rcases h31 h31' with rfl | rfl | rfl | rfl
    ·
      refine fieldInnerT_of_not_sq_dvd hnab hp ?_ ?_
      · rw [hcard, show Nat.card (NativeSporadic.Carrier .J4) = _ from CFSG.Sporadic.J4.card_J4]
        decide +kernel
      · intro hd
        have hJ4 : Nonempty (T ≃* NativeSporadic.J4) := ⟨e⟩
        have := (CFSG.Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes
          hJ4).1 5 hp hd
        omega
    ·
      refine fieldInnerT_of_not_sq_dvd hnab hp ?_ ?_
      · rw [hcard, show Nat.card (NativeSporadic.Carrier .ONan) = _ from
          CFSG.Sporadic.ON.card_ON_eq]
        decide +kernel
      · intro hd
        have hcardOut : Nat.card (Outer T) = Nat.card (Outer (NativeSporadic.Carrier .ONan)) :=
          Nat.card_congr (equivalence e).toEquiv
        rw [hcardOut] at hd
        have := Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent 5 hp hd
        omega
    ·
      have hcardTh : Nat.card T = 90745943887872000 := by
        rw [hcard]; exact CTP.card_Th
      exact fieldInnerT_Th_five hcardTh
    ·
      exact fieldInnerT_Ly_five hnab ⟨e⟩
  · exact fieldInnerT_of_dvd_N71 hp hp5 (hcard ▸ hN71) fun h5' hd => h5 ⟨h5', hcard ▸ hd⟩

end Main

end CFSG.RankThree.PartOne.FOCD
