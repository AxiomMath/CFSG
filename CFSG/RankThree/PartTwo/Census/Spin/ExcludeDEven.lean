module

public import CFSG.RankThree.PartTwo.Census.Spin.Exclude
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessD
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem typeD_mk_data (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid) :
    (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.characteristic = q.p ∧
      (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.fieldOrder = q.p ^ q.exponent ∧
      (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.fieldExponent = q.exponent ∧
      (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.rank = r :=
  ⟨LieTypeIndex.characteristic_D r q, (LieTypeIndex.fieldOrder_D r q).trans q.card_def,
    LieTypeIndex.fieldExponent_D r q, rfl⟩

theorem excluded433_D_even (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid)
    (hp : q.p = 2) (hf : 2 ≤ q.exponent) : Excluded433 (.lie ⟨.D r q, hv⟩) := by
  obtain ⟨hchar, hord, -, hrank⟩ := typeD_mk_data r q hv
  rw [hp] at hchar hord
  have hq4 : 4 ≤ (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.fieldOrder := by
    rw [hord]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
  have h4 : 4 ≤ r := TypeDDiagramLieIndex.four_le_rank
    (TypeDLieIndex.toTypeDDiagramLieIndex ⟨⟨.D r q, hv⟩, by simp⟩)
  obtain ⟨s, hs, hs2, -, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf
  rcases (show r = 4 ∨ r = 5 ∨ 6 ≤ r by omega) with h | h | h
  · refine excluded433_D_of_four hv hs hs2 (le_of_eq ?_)
      (CarrierD.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd) id id
        (CarrierD.det_full_ne_zero _ (hrank.trans h) hs hs2))
    rw [Fintype.card_fin, hrank, h]
  · exact excluded433_D_of_four hv hs hs2 (le_of_eq (Fintype.card_fin 4).symm)
      (CarrierD.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd)
        (fun c : Fin 4 => ⟨c, by omega⟩) (fun a : Fin 4 => ⟨a + 1, by omega⟩)
        (CarrierD.det_five_ne_zero _ (hrank.trans h) hs hs2))
  · exact excluded433_D_of_four hv hs hs2 (le_of_eq (Fintype.card_fin 4).symm)
      (CarrierD.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd)
        (fun c : Fin 4 => ⟨c, by omega⟩) (fun a : Fin 4 => ⟨a + 1, by omega⟩)
        (CarrierD.det_tri_ne_zero _ h hs))

end CFSG.RankThree.PartTwo.Census.Spin
