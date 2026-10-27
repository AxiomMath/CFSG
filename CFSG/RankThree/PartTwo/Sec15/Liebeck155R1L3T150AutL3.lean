module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150AutL3SU
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CoverRank
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Cfg

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)

theorem isPerfect_of_isoLThreePi {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n : ℕ}
    (hn : 1 ≤ n) (h : IsoLThreePi X 2 n) : Group.IsPerfect X := by
  rcases h with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · have := (Sec13.isPerfect_center_projSL 2 n hn hq).1
    exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  · by_cases hq2 : 2 < 2 ^ n
    · have := (Sec13.isPerfect_center_projSU 2 n hn hq hq2).1
      exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    · exfalso
      have hn1 : n = 1 := by
        have h2 : 2 ^ n = 2 ^ 1 := by
          have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
          omega
        exact Nat.pow_right_injective le_rfl h2
      subst hn1
      have := Sec13.isSolvable_projSU_two
      have hsolv : Group.IsSolvable X :=
        solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      have hcomm : ∀ a b : X, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.mpr hsolv
      let : CommGroup X := { ‹Group X› with mul_comm := hcomm }
      have hprime : (Nat.card X).Prime := IsSimpleGroup.prime_card
      have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 1 le_rfl
      have hcard : Nat.card X = 72 := by
        rw [Nat.card_congr φ.toEquiv]
        norm_num at hc
        omega
      rw [hcard] at hprime
      norm_num at hprime

theorem noTwoCentAut_of_survL3_subnormal {S : Type} [Group S]
    [Finite S] {σ : MulAut S} {K : Subgroup S} (hK : K ≤ Sec4.autFix σ) (hKs : IsSimpleGroup ↥K)
    (hsub : (K.subgroupOf (Sec4.autFix σ)).IsSubnormal) (hodd : Odd (orderOf σ))
    (h : Sec4.RonanK429.SurvL3 S σ K) : NoTwoCentAut K := by
  obtain ⟨n, hn, hKiso, hSiso, hfield⟩ := h
  have : Group.IsPerfect K := isPerfect_of_isoLThreePi hn hKiso
  have hnt : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).mp hKs.toNontrivial
  rcases hfield with ⟨F, _, _, e, hk⟩ | ⟨p, f, F, _, h, hq, e, hk⟩
  · exact noTwoCentAut_of_field_linear hK hnt hsub hodd e hk
  · obtain rfl := Sec4.RonanK429.eq_two_of_isoLThreePi_of_unitaryPSU hn hSiso h e
    exact noTwoCentAut_of_field_unitary hK hnt hsub hodd h hq e hk

theorem noTwoCentAut_of_survL3_pow_three {S : Type} [Group S]
    [Finite S] {σ : MulAut S} {K : Subgroup S} (hK : K ≤ Sec4.autFix σ) (hKs : IsSimpleGroup ↥K)
    (hsub : (K.subgroupOf (Sec4.autFix σ)).IsSubnormal) (hσ : σ ^ 3 = 1)
    (h : Sec4.RonanK429.SurvL3 S σ K) : NoTwoCentAut K :=
  noTwoCentAut_of_survL3_subnormal hK hKs hsub
    (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hσ)) h

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150
