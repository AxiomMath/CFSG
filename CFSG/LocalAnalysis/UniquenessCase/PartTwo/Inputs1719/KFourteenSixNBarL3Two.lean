module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BT
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdBorelL3
import CFSG.Quasithin.Background.C35InspSmall
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.NumberTheory.TwoPowAddOneOdd
import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar

open CFSG.Blueprint

variable {X : Type} [Group X] [Finite X]

theorem odd_of_two_pow_mod_three_eq_two {f : ℕ} (hf : 2 ^ f % 3 = 2) : Odd f := by
  rcases Nat.even_or_odd f with he | ho
  · have h := CFSG.two_pow_mod_three_of_even he
    omega
  · exact ho

omit [Finite X] in
theorem two_le_f_of_lieModel_psl3_two {f r : ℕ} (hX : LieModel X .PSL 3 2 f) (hr : r.Prime)
    (hr11 : 11 ≤ r) {A : Subgroup X} (hA : Nat.card A = r) : 2 ≤ f := by
  have hf1 : 1 ≤ f := hX.admissible.2.1
  have hfne : f ≠ 1 := by
    rintro rfl
    have hcardX : Nat.card X = 168 := hX.card_psl_three_two
    have hdvd : r ∣ Nat.card X := hA ▸ Subgroup.card_subgroup_dvd_card A
    rw [hcardX, show (168 : ℕ) = 2 ^ 3 * 3 * 7 by norm_num] at hdvd
    rcases hr.dvd_mul.1 hdvd with h | h
    · rcases hr.dvd_mul.1 h with h | h
      · have hr2 : r = 2 :=
          (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)
        omega
      · have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h
        omega
    · have hr7 : r = 7 :=
        (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 7)).1 h
      omega
  omega

theorem false_of_lieModel_psl3_two [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    {f r : ℕ} (hX : LieModel X .PSL 3 2 f) (hf : 2 ^ f % 3 = 2) (hr : r.Prime) (hr3 : 3 < r)
    (hn : ∃ n : ℕ, Odd n ∧ r ∣ 2 ^ n + 1) {A U : Subgroup X} (hA : Nat.card A = r)
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) (hAU : UC22.Permutes A U) : False := by
  obtain ⟨n, hnodd, hrn⟩ := hn
  have hr11 : 11 ≤ r :=
    CFSG.NumberTheory.eleven_le_of_dvd_two_pow_add_one hr hr3 hnodd hrn
  have hr2 : r ≠ 2 := by omega
  have hf2 : 2 ≤ f := two_le_f_of_lieModel_psl3_two hX hr hr11 hA
  have hfodd : Odd f := odd_of_two_pow_mod_three_eq_two hf
  have hAodd : Odd (Nat.card A) := by
    rw [hA]
    exact hr.odd_of_ne_two hr2
  have hInf : A ⊓ U = ⊥ := UC22.uc22p2214_inf_eq_bot_of_odd hAodd hU.isPGroup
  obtain ⟨k, hk⟩ := hU.isPGroup.exists_card_eq
  have hcardH : Nat.card ↥(A ⊔ U) = r * 2 ^ k := by
    rw [UC22.uc22p2214_card_sup_of_permutes hAU hInf, hA, hk]
  have hsolv : Group.IsSolvable ↥(A ⊔ U) := by
    refine CFSG.Quasithin.C35Pf.isSolvable_of_card_pow_mul_pow (p := 2) (q := r)
      (a := k) (b := 1) Nat.prime_two hr (by omega) ?_
    rw [hcardH, mul_comm, pow_one]
  have hBT : UC22.F10.K108BT (fun S _ => LieModel S .PSL 3 2 f) :=
    UC22.F10.k108BT_of_lieModel (F := fun S _ => LieModel S .PSL 3 2 f) (by
      intro S _ hS
      exact ⟨.PSL, 3, f, hf2, Or.inl rfl, hS⟩)
  have hAN : A ≤ Subgroup.normalizer (U : Set X) := by
    have h := hBT X (inferInstance : IsSimpleGroup X) hnab hX U hU (A ⊔ U) le_sup_right hsolv
    exact fun a ha => h (Subgroup.mem_sup_left ha)
  have hUcard : Nat.card U = 2 ^ (Nat.card X).factorization 2 := by
    have h := CFSG.ABGLocalTools.IsSylowOf.card_eq hU
    rwa [Subgroup.card_top] at h
  let S : Sylow 2 X := Sylow.ofCard U hUcard
  have hScoe : (S : Subgroup X) = U := Sylow.coe_ofCard U hUcard
  have hAbot : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card A = 1 := by rw [hbot]; simp
    omega
  obtain ⟨a, ha, ha1⟩ := (Subgroup.bot_or_exists_ne_one A).resolve_left hAbot
  have hpowU : a ^ (2 ^ f - 1) ∈ U := by
    have hb : a ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
      rw [hScoe]
      exact hAN ha
    have h := UC22.KOB.pow_mem_of_mem_normalizer_L3 (hX := hX) S hb
    rwa [hScoe] at h
  have hpow1 : a ^ (2 ^ f - 1) = 1 := by
    have hmem : a ^ (2 ^ f - 1) ∈ A ⊓ U := ⟨A.pow_mem ha _, hpowU⟩
    rw [hInf, Subgroup.mem_bot] at hmem
    exact hmem
  have horddvd : orderOf a ∣ r := by
    rw [← hA]
    exact Subgroup.orderOf_dvd_natCard A ha
  have hord : orderOf a = r := by
    rcases hr.eq_one_or_self_of_dvd (orderOf a) horddvd with h | h
    · rw [orderOf_eq_one_iff] at h
      exact absurd h ha1
    · exact h
  refine CFSG.NumberTheory.not_dvd_two_pow_sub_one_of_dvd_two_pow_add_one hr hr2 hrn hfodd ?_
  rw [← hord]
  exact orderOf_dvd_iff_pow_eq_one.mpr hpow1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar
