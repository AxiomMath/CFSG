module

public import CFSG.Quasithin.Background.A318POutCheap
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.Sporadic.Schreier.J4SOuter

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

namespace A318P

theorem not_dvd_outer_M11
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M11)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) :=
  not_dvd_outer_of_carrier e CFSG.Sporadic.Schreier.at_m11_schreier.1 hp hp2

theorem not_dvd_outer_M12
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M12)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) :=
  not_dvd_outer_of_carrier e (CFSG.ComponentClassification.M12Cover.card_outer.le) hp hp2

theorem not_dvd_outer_M22
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M22)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) := by
  have : Finite (NativeSporadic.Carrier .M22) := Finite.of_equiv S e.toEquiv
  exact not_dvd_outer_of_carrier e (card_outer_le_two_of_card_mulAut_le
    CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card) hp hp2

theorem not_dvd_outer_M23
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M23)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) :=
  not_dvd_outer_of_carrier e CFSG.Sporadic.Schreier.at_m23_schreier.1 hp hp2

theorem not_dvd_outer_M24
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M24)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) := by
  have : Finite (NativeSporadic.Carrier .M24) := Finite.of_equiv S e.toEquiv
  exact not_dvd_outer_of_carrier e (card_outer_le_two_of_card_mulAut_le
    CFSG.Sporadic.Schreier.m24_center_eq_bot'
    (CFSG.Sporadic.Schreier.m24_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num)))) hp hp2

theorem not_dvd_outer_J1
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .J1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) :=
  not_dvd_outer_of_carrier e (CFSG.Sporadic.Schreier.at_j1_schreier.1.le.trans (by norm_num)) hp hp2

theorem not_dvd_outer_J2
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .J2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) :=
  not_dvd_outer_of_carrier e CFSG.Sporadic.Schreier.AT_J2_Schreier.1 hp hp2

theorem not_dvd_outer_J4
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .J4)
    (h3 : ¬ 3 ∣ Nat.card (Outer (NativeSporadic.Carrier .J4))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) := by
  intro h
  rw [Nat.card_congr (equivalence e).toEquiv] at h
  have hT : Nonempty (NativeSporadic.Carrier .J4 ≃* NativeSporadic.J4) := ⟨MulEquiv.refl _⟩
  rcases (CFSG.Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes hT).1 p hp h
    with rfl | rfl
  · exact hp2 rfl
  · exact h3 h

end A318P

end CFSG.Quasithin
