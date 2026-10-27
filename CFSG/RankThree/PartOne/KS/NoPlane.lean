module

public import CFSG.RankThree.PartOne.KS.Assembly
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.RankThree.GroupTheory.SteinbergBMJ3ComponentCentralization
import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.Schreier.PairJ3Faithful

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree.LocalRank
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise

@[expose] def NoPlaneAut (A : Type) [Group A] : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    Nonempty (T ≃* A) → ∀ p : ℕ, p.Prime → 3 < p → ¬ p ^ 2 ∣ Nat.card (MulAut T)

theorem sporadicPlaneOdd_of_noPlaneAut {A : Type} [Group A] (h : NoPlaneAut A) :
    SporadicPlaneOdd A := fun T _ _ _ hnab hTA p hp hp3 =>
  planeLocalCoreOdd_of_not_sq_dvd (h T hnab hTA p hp hp3)

theorem noPlaneAut_of_outer_le {A : Type} [Group A] {N k : ℕ} (hN : Nat.card A = N)
    (hk : Nat.card (Outer A) ≤ k) (hpN : ∀ p : ℕ, p.Prime → 3 < p → k < p ∧ ¬ p ^ 2 ∣ N) :
    NoPlaneAut A := by
  intro T _ _ _ hnab ⟨e⟩ p hp hp3
  exact not_sq_dvd_card_mulAut_of_outer_le hnab e hN hk hp (hpN p hp hp3).1 (hpN p hp hp3).2

theorem four_lt_of_prime_of_three_lt {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 4 < p := by
  rcases Nat.lt_or_ge 4 p with h | h
  · exact h
  · have : p = 4 := by omega
    subst this
    norm_num at hp

theorem noPlaneAut_M11 : NoPlaneAut (Carrier .M11) :=
  noPlaneAut_of_outer_le (N := 7920) (k := 2) CFSG.Sporadic.Schreier.m11_card
    CFSG.Sporadic.Schreier.at_m11_schreier.1 fun p hp hp3 =>
      ⟨by omega, by
        have := not_sq_dvd_two_pow_three_pow_mul (a := 4) (b := 2) (m := 55) (B := 7) hp hp3
          (by norm_num) (by decide) (by norm_num)
        norm_num at this
        exact this⟩

theorem noPlaneAut_M12 : NoPlaneAut (Carrier .M12) :=
  noPlaneAut_of_outer_le (N := 95040) (k := 4) CFSG.Sporadic.Schreier.m12_card
    CFSG.Sporadic.Schreier.at_m12_schreier.1 fun p hp hp3 =>
      ⟨four_lt_of_prime_of_three_lt hp hp3, by
        have := not_sq_dvd_two_pow_three_pow_mul (a := 6) (b := 3) (m := 55) (B := 7) hp hp3
          (by norm_num) (by decide) (by norm_num)
        norm_num at this
        exact this⟩

theorem noPlaneAut_M22 : NoPlaneAut (Carrier .M22) :=
  noPlaneAut_of_outer_le (N := 443520) (k := 4) CFSG.Sporadic.Schreier.m22_card
    CFSG.Sporadic.Schreier.at_m22_schreier.1 fun p hp hp3 =>
      ⟨four_lt_of_prime_of_three_lt hp hp3, by
        have := not_sq_dvd_two_pow_three_pow_mul (a := 7) (b := 2) (m := 385) (B := 19) hp hp3
          (by norm_num) (by decide) (by norm_num)
        norm_num at this
        exact this⟩

theorem noPlaneAut_M23 : NoPlaneAut (Carrier .M23) :=
  noPlaneAut_of_outer_le (N := 10200960) (k := 2) CFSG.Sporadic.Schreier.m23_card
    CFSG.Sporadic.Schreier.at_m23_schreier.1 fun p hp hp3 =>
      ⟨by omega, by
        have := not_sq_dvd_two_pow_three_pow_mul (a := 7) (b := 2) (m := 8855) (B := 94) hp hp3
          (by norm_num) (by decide) (by norm_num)
        norm_num at this
        exact this⟩

theorem noPlaneAut_M24 : NoPlaneAut (Carrier .M24) :=
  noPlaneAut_of_outer_le (N := 244823040) (k := 4) CFSG.Sporadic.Schreier.m24_card
    CFSG.Sporadic.Schreier.at_m24_schreier.1 fun p hp hp3 =>
      ⟨four_lt_of_prime_of_three_lt hp hp3, by
        have := not_sq_dvd_two_pow_three_pow_mul (a := 10) (b := 3) (m := 8855) (B := 94) hp hp3
          (by norm_num) (by decide) (by norm_num)
        norm_num at this
        exact this⟩

theorem noPlaneAut_J1 : NoPlaneAut (Carrier .J1) :=
  noPlaneAut_of_outer_le (N := 175560) (k := 1)
    ((Nat.card_congr CFSG.Sporadic.Schreier.j1PermEquiv.toEquiv).trans
      CFSG.Sporadic.Schreier.card_j1P)
    CFSG.Sporadic.Schreier.at_j1_schreier.1.le fun p hp hp3 =>
      ⟨by omega, by
        have := not_sq_dvd_two_pow_three_pow_mul (a := 3) (b := 1) (m := 7315) (B := 85) hp hp3
          (by norm_num) (by decide) (by norm_num)
        norm_num at this
        exact this⟩

theorem noPlaneAut_J3 : NoPlaneAut (Carrier .J3) := by
  intro T _ _ _ _ ⟨e⟩ p hp hp3
  obtain ⟨-, -, -, -, hAut⟩ :=
    CFSG.Sporadic.SmallOddCore.ctuc_j3_full_automorphism_permutation_model
  have hcard : Nat.card (MulAut T) = 100465920 := by
    rw [← hAut]
    exact Nat.card_congr (MulAut.congr (e.trans CFSG.Sporadic.Schreier.j3PermEquiv)).toEquiv
  rw [hcard]
  exact CFSG.RankThree.GroupTheory.SteinbergBM.not_sq_dvd_card_mulAut_J3 hp hp3

theorem sporadicPlaneOdd_M11 : SporadicPlaneOdd (Carrier .M11) :=
  sporadicPlaneOdd_of_noPlaneAut noPlaneAut_M11

theorem sporadicPlaneOdd_M12 : SporadicPlaneOdd (Carrier .M12) :=
  sporadicPlaneOdd_of_noPlaneAut noPlaneAut_M12

theorem sporadicPlaneOdd_M22 : SporadicPlaneOdd (Carrier .M22) :=
  sporadicPlaneOdd_of_noPlaneAut noPlaneAut_M22

theorem sporadicPlaneOdd_M23 : SporadicPlaneOdd (Carrier .M23) :=
  sporadicPlaneOdd_of_noPlaneAut noPlaneAut_M23

theorem sporadicPlaneOdd_M24 : SporadicPlaneOdd (Carrier .M24) :=
  sporadicPlaneOdd_of_noPlaneAut noPlaneAut_M24

theorem sporadicPlaneOdd_J1 : SporadicPlaneOdd (Carrier .J1) :=
  sporadicPlaneOdd_of_noPlaneAut noPlaneAut_J1

theorem sporadicPlaneOdd_J3 : SporadicPlaneOdd (Carrier .J3) :=
  sporadicPlaneOdd_of_noPlaneAut noPlaneAut_J3

end CFSG.RankThree.PartOne
