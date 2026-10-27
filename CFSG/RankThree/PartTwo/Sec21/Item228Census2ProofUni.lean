module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofL3Type
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofRee

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projSL)


namespace Item228Census2Proof

theorem five_dvd_card_thetaQuot {G : Type} [Group G] [Finite G] {X K : Subgroup G} {m : ℕ}
    (hKX : K ≤ X) (hKm : Nonempty (K ≃* projSL 2 (GaloisField 2 m))) (hm0 : 0 < m)
    (hme : Even m) : 5 ∣ Nat.card (X ⧸ aschbacherSolvableCore 3 X) := by
  obtain ⟨eK⟩ := hKm
  have : IsSimpleGroup (projSL 2 (GaloisField 2 m)) :=
    isSimpleGroup_projSL_two (by obtain ⟨r, hr⟩ := hme; omega)
  have : IsSimpleGroup K := eK.isSimpleGroup
  have hK3 : 3 ∣ Nat.card K := by
    rw [Nat.card_congr eK.toEquiv]
    exact Item22Res4Proof.three_dvd_card_projSL_two hm0
  have hK5 : 5 ∣ Nat.card K := by
    rw [Nat.card_congr eK.toEquiv]
    exact Item22Res4Proof.five_dvd_card_projSL_two hm0 hme
  have hι := Item22Res4Proof.injective_of_three_dvd hKX hK3
  have h1 : Nat.card (K.subgroupOf X) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
  have h2 : Nat.card (K.subgroupOf X) ∣ Nat.card (X ⧸ aschbacherSolvableCore 3 X) := by
    rw [← Nat.card_range_of_injective hι]
    exact Subgroup.card_subgroup_dvd_card
      ((QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp (K.subgroupOf X).subtype).range
  exact hK5.trans (h1 ▸ h2)

theorem odd_of_three_dvd_two_pow_add_one {n : ℕ} (h : 3 ∣ 2 ^ n + 1) : Odd n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ho
  · exfalso
    have : (2 ^ (k + k) + 1) % 3 = 2 := by
      rw [← two_mul, pow_mul]
      norm_num [Nat.add_mod, Nat.pow_mod]
    omega
  · exact ho

theorem not_five_dvd_card_unitary_three {n : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 n K)
    (h3 : 3 ∣ 2 ^ n + 1) :
    ¬ 5 ∣ Nat.card (unitarySU 2 n K 3) ∧ ¬ 5 ∣ Nat.card (unitaryPSU hK 3) := by
  obtain ⟨a, rfl⟩ := odd_of_three_dvd_two_pow_add_one h3
  have hcard : Nat.card K = (2 ^ (2 * a + 1)) ^ 2 := by rw [hK.card, ← pow_mul, mul_comm]
  have hSU := not_five_dvd_card_statedSU_three hcard
  refine ⟨hSU, fun h5 => hSU ?_⟩
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup (unitaryScalars hK 3)
  exact h5.trans (Dvd.intro _ this.symm)

end Item228Census2Proof

open Item228Census2Proof

section Certs


theorem census228L3TypeFor_of_not_five_dvd {P : (Y : Type) → [Group Y] → Prop}
    (h : ∀ (Y : Type) [Group Y] [Finite Y], P Y → ¬ 5 ∣ Nat.card Y) : Census228L3TypeFor P := by
  intro G _ _ X A K K₀ m _ hP _ _ _ _ _ _ _ ρ _ _ hKK hK0X _ _ _ hKm hm0 hme
  exact (h _ hP (five_dvd_card_thetaQuot (hKK.trans hK0X) hKm hm0 hme)).elim

theorem census228L3TypeUniTwo_holds : Census228L3TypeUniTwo := by
  refine census228L3TypeFor_of_not_five_dvd fun Y _ _ hY => ?_
  obtain ⟨n, K, _, hK, h3, ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩⟩ := hY
  · rw [Nat.card_congr e.toEquiv]
    exact (not_five_dvd_card_unitary_three hK h3).2
  · rw [Nat.card_congr e.toEquiv]
    exact (not_five_dvd_card_unitary_three hK h3).1

end Certs

end CFSG.RankThree.PartTwo.Sec21
