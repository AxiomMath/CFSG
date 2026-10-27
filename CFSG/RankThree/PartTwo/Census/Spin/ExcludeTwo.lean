module

public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeBEven
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeDEven
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeTD
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessBShort
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTDFour

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem excluded433_D_two (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid)
    (hp : q.p = 2) (h5 : 5 ≤ r) : Excluded433 (.lie ⟨.D r q, hv⟩) := by
  obtain ⟨hchar, -, -, hrank⟩ := typeD_mk_data r q hv
  rcases (show r = 5 ∨ 6 ≤ r by omega) with h | h6
  · exact excluded433_D_of_four hv Nat.prime_three (by norm_num) le_rfl
      (CarrierD.hasWitness_five _ (hchar.trans hp) (by rw [hrank]; exact h))
  · exact excluded433_D_of_four hv Nat.prime_three (by norm_num) le_rfl
      (CarrierD.hasWitness_three _ (hchar.trans hp) (by rw [hrank]; exact h6))

theorem excluded433_B_two (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hp : q.p = 2) (h5 : 5 ≤ r) : Excluded433 (.lie ⟨.B r q, hv⟩) := by
  obtain ⟨hchar, -, -, hrank⟩ := typeB_mk_data r q hv
  exact excluded433_B_of_four hv Nat.prime_three (by norm_num) le_rfl
    (CarrierB.hasWitness_short _ (hchar.trans hp) (by omega))

theorem excluded433_twistedD_two (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (hp : q.p = 2) (h6 : 6 ≤ r) :
    Excluded433 (.lie ⟨.twistedD r q, hv⟩) := by
  obtain ⟨hchar, -, -, hrank⟩ := typeTwistedD_mk_data r q hv
  exact excluded433_twistedD_of_four hv Nat.prime_three (by norm_num) le_rfl
    (CarrierTD.hasWitness_twShort _ (hchar.trans hp) (by rw [hrank]; exact h6))

theorem excluded433_twistedD_five_two (q : PrimePower) (hv : (LieTypeIndex.twistedD 5 q).Valid)
    (hp : q.p = 2) (hf : q.exponent = 1) : Excluded433 (.lie ⟨.twistedD 5 q, hv⟩) := by
  obtain ⟨hchar, -, hexp, hrank⟩ := typeTwistedD_mk_data 5 q hv
  exact excluded433_twistedD_of_four hv Nat.prime_three (by norm_num) le_rfl
    (CarrierTD.hasWitness_tdfive _ (hchar.trans hp) (hexp.trans hf) hrank)

theorem excluded433_twistedD_four_four (q : PrimePower)
    (hv : (LieTypeIndex.twistedD 4 q).Valid) (hp : q.p = 2) (hf : q.exponent = 2) :
    Excluded433 (.lie ⟨.twistedD 4 q, hv⟩) := by
  obtain ⟨hchar, -, hexp, -⟩ := typeTwistedD_mk_data 4 q hv
  exact excluded433_twistedD_of_three hv Nat.prime_five (by norm_num) le_rfl
    (CarrierTD.hasWitness_tdfour _ (hchar.trans hp) (hexp.trans hf))

end CFSG.RankThree.PartTwo.Census.Spin
