module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowF4ReeList
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECArith
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Open
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Ree

theorem lieOrderNumerator_twistedF4 (q : ℕ) :
    lieOrderNumerator .twistedF4 0 q = q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) :=
  rfl

theorem lieOrderDivisor_twistedF4 (q : ℕ) : lieOrderDivisor .twistedF4 0 q = 1 := rfl

theorem lieOrderNumerator_twistedF4_pow_three (q : ℕ) (hq : 1 ≤ q) :
    lieOrderNumerator .twistedF4 0 (q ^ 3) = lieOrderNumerator .twistedF4 0 q *
      (q ^ 24 * (q ^ 12 - q ^ 6 + 1) * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - q ^ 3 + 1) *
        (q ^ 2 + q + 1)) := by
  rw [lieOrderNumerator_twistedF4, lieOrderNumerator_twistedF4]
  have h1 : q ^ 6 ≤ q ^ 12 := Nat.pow_le_pow_right hq (by norm_num)
  have h2 : q ^ 3 ≤ q ^ 6 := Nat.pow_le_pow_right hq (by norm_num)
  have h3 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have h4 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  have h5 : 1 ≤ (q ^ 3) ^ 4 := Nat.one_le_pow _ _ h4
  zify [hq, h1, h2, h3, h4, h5]
  ring

theorem three_dvd_eight_add_four_add_one (q : ℕ) (hq : q % 3 = 2) : 3 ∣ q ^ 8 + q ^ 4 + 1 := by
  apply Nat.dvd_of_mod_eq_zero
  norm_num [Nat.add_mod, Nat.pow_mod, hq]

theorem three_mul_lieOrderNumerator_twistedF4_dvd (q : ℕ) (hq : q % 3 = 2) :
    3 * lieOrderNumerator .twistedF4 0 q ∣ lieOrderNumerator .twistedF4 0 (q ^ 3) := by
  have hq1 : 1 ≤ q := by omega
  rw [lieOrderNumerator_twistedF4_pow_three q hq1, mul_comm 3]
  apply mul_dvd_mul_left
  exact ((Dvd.dvd.mul_left (three_dvd_eight_add_four_add_one q hq)
    (q ^ 24 * (q ^ 12 - q ^ 6 + 1))).mul_right _).mul_right _

section Outer


theorem outerRow_of_lieModel_twistedF4 {S : Type} [Group S] [Finite S] {m : ℕ}
    (hadm : StatedLieAdmissible .twistedF4 0 2 (2 * m + 1))
    (hLie : LieModel S .twistedF4 0 2 (2 * m + 1)) (hZ : Subgroup.center S = ⊥) : OuterRow S := by
  have hcard : Nat.card S = lieOrderNumerator .twistedF4 0 (2 ^ (2 * m + 1)) := by
    have h := CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover.card_of_lieModel hLie
    rw [lieOrderDivisor_twistedF4, mul_one] at h
    exact h
  refine outerRow_of_fixed_card_dvd hZ fun σ hσ hout => ?_
  rcases HardMathSupport.Lang.Coordinator.outerFixedOrderBoundAt_twistedF4 S 0 2 (2 * m + 1)
      hadm hLie (by decide) 3 Nat.prime_three (by decide)
      (by rw [lieOrderDivisor_twistedF4]; norm_num) (by simp) σ hσ hout with
    ⟨f₀, hf₀, hdvd⟩ | ⟨h1, -⟩
  · refine ⟨fixedSubgroup σ, lieOrderNumerator .twistedF4 0 (2 ^ f₀), fun x => Iff.rfl, hdvd, ?_⟩
    have hq3 : 2 ^ f₀ % 3 = 2 := by
      obtain ⟨k, hk⟩ : ∃ k, f₀ = 2 * k + 1 := ⟨f₀ / 2, by omega⟩
      rw [hk]
      exact two_pow_odd_mod_three k
    have hpow : 2 ^ (2 * m + 1) = (2 ^ f₀) ^ 3 := by
      rw [hf₀, mul_comm, pow_mul]
    rw [hcard, hpow]
    exact three_mul_lieOrderNumerator_twistedF4_dvd (2 ^ f₀) hq3
  · exact absurd h1 (by decide)

end Outer

section Row


theorem rowOf_f4_ree (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid) :
    RowOf (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group := by
  intro S _ _ hs hna ⟨e⟩
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      have ha : a ∈ Subgroup.center S := by
        rw [h]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hm e
  obtain ⟨-, a, -, -, K, _, _, _, hK, ⟨e'⟩⟩ := exists_mulEquiv_reeGamma hR
  have hLie : Blueprint.LieModel S .twistedF4 0 2 (2 * m + 1) :=
    Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))
  exact ⟨ListRow.of_mulEquiv e'.symm (listRow_reeGamma a K hK),
    outerRow_of_lieModel_twistedF4 hR.1 hLie hZ⟩

end Row


end CFSG.RankThree.PartTwo.Sec4.RonanK432
