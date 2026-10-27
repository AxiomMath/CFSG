module

public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeBEven
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeDEven
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessDTheta
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessBThree

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem excluded433_B_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hr : 3 ≤ r) (hp : q.p ≠ 2) : Excluded433 (.lie ⟨.B r q, hv⟩) := by
  obtain ⟨hchar, -, hexp, hrank⟩ := typeB_mk_data r q hv
  have hodd : (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.characteristic ≠ 2 := hchar ▸ hp
  have hpr := (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.characteristic_prime
  have hf1 := q.exponent_pos
  by_cases h4 : 4 ≤ r
  · exact excluded433_B_of_four hv hpr hodd (by rw [hexp]; omega)
      (CarrierB.hasWitness_theta_four _ hodd (by omega))
  · exact excluded433_B_of_four hv hpr hodd (by rw [hexp]; omega)
      (CarrierB.hasWitness_bthree _ hodd (by omega))

theorem excluded433_D_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid)
    (hp : q.p ≠ 2) : Excluded433 (.lie ⟨.D r q, hv⟩) := by
  obtain ⟨hchar, -, hexp, -⟩ := typeD_mk_data r q hv
  have hodd : (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.characteristic ≠ 2 := hchar ▸ hp
  have hf1 := q.exponent_pos
  exact excluded433_D_of_four hv (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.characteristic_prime
    hodd (by rw [hexp]; omega) (CarrierD.hasWitness_theta_four _ hodd)

end CFSG.RankThree.PartTwo.Census.Spin
