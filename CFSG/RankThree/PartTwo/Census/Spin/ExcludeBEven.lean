module

public import CFSG.RankThree.PartTwo.Census.Spin.Exclude
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessB
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem typeB_mk_data (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid) :
    (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.characteristic = q.p ∧
      (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.fieldOrder = q.p ^ q.exponent ∧
      (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.fieldExponent = q.exponent ∧
      TypeBLieIndex.carrierRank ⟨⟨.B r q, hv⟩, trivial⟩ + 1 = r :=
  ⟨LieTypeIndex.characteristic_B r q, (LieTypeIndex.fieldOrder_B r q).trans q.card_def,
    LieTypeIndex.fieldExponent_B r q, TypeBLieIndex.carrierRank_add_one _⟩

theorem excluded433_B_even (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hr : 3 ≤ r) (hp : q.p = 2) (hf : 2 ≤ q.exponent) (h34 : ¬ (r = 3 ∧ q.exponent = 2)) :
    Excluded433 (.lie ⟨.B r q, hv⟩) := by
  obtain ⟨hchar, hord, -, hrank⟩ := typeB_mk_data r q hv
  rw [hp] at hchar hord
  have hq4 : 4 ≤ (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.fieldOrder := by
    rw [hord]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
  rcases (show r = 3 ∨ 4 ≤ r by omega) with rfl | hr4
  ·
    have hf3 : 3 ≤ q.exponent := by omega
    obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_sub_one hf3
    refine excluded433_B_of_three hv hs (by omega) (le_of_eq ?_)
      (CarrierB.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd) id id
        (CarrierB.det_full_ne_zero _ (by omega) hs (by omega)))
    rw [Fintype.card_fin, hrank]
  · obtain ⟨s, hs, hs2, -, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf
    rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
    · refine excluded433_B_of_four hv hs hs2 (le_of_eq ?_)
        (CarrierB.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd) id id
          (CarrierB.det_full_ne_zero _ (by omega) hs hs2))
      rw [Fintype.card_fin, hrank]
    · exact excluded433_B_of_four hv hs hs2 (le_of_eq (Fintype.card_fin 4).symm)
        (CarrierB.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd)
          (fun c : Fin 4 => ⟨c, by omega⟩) (fun a : Fin 4 => ⟨a + 1, by omega⟩)
          (CarrierB.det_tri_ne_zero _ (by omega) hs))

end CFSG.RankThree.PartTwo.Census.Spin
