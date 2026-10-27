module

public import CFSG.RankThree.PartOne.Census3.OpenCases
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeBEven
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeDEven
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeTD
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessBThree
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessDTheta

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartTwo.Census CFSG.RankThree.PartTwo.Census.Spin CFSG.Assembly TauCeti

theorem four_le_twoLocalOddRank_of_hasWitness {d : ValidLieTypeIndex} {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : 4 ≤ k) (h : HasWitness d.Group p k) [Finite (CFSGIndex.lie d).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie d).Group := by
  have hfin : Finite d.Group := inferInstanceAs (Finite (CFSGIndex.lie d).Group)
  exact Census3.four_le_twoLocalOddRank_of_localRank hp hp2
    (hk.trans (le_localRank_of_hasWitness hp h))

section Families

variable {r : ℕ} {q : PrimePower} {p k : ℕ}

theorem rankFour_B_of_four (hv : (LieTypeIndex.B r q).Valid) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 4 ≤ k) (h : HasWitness (TypeBLieIndex.Group ⟨⟨.B r q, hv⟩, trivial⟩) p k)
    [Finite (CFSGIndex.lie ⟨.B r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.B r q, hv⟩).Group :=
  four_le_twoLocalOddRank_of_hasWitness hp hp2 hk h

theorem rankFour_D_of_four (hv : (LieTypeIndex.D r q).Valid) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 4 ≤ k) (h : HasWitness (TypeDLieIndex.Group ⟨⟨.D r q, hv⟩, by simp⟩) p k)
    [Finite (CFSGIndex.lie ⟨.D r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.D r q, hv⟩).Group :=
  four_le_twoLocalOddRank_of_hasWitness hp hp2 hk h

theorem rankFour_twistedD_of_four (hv : (LieTypeIndex.twistedD r q).Valid) (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : 4 ≤ k)
    (h : HasWitness (TypeTwistedDLieIndex.Group ⟨⟨.twistedD r q, hv⟩, by simp⟩) p k)
    [Finite (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group :=
  four_le_twoLocalOddRank_of_hasWitness hp hp2 hk h

end Families

theorem rankFour_B_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid) (hr : 3 ≤ r)
    (hp : q.p ≠ 2) [Finite (CFSGIndex.lie ⟨.B r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.B r q, hv⟩).Group := by
  obtain ⟨hchar, -, hexp, hrank⟩ := typeB_mk_data r q hv
  have hodd : (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.characteristic ≠ 2 := hchar ▸ hp
  have hpr := (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.characteristic_prime
  have hf1 := q.exponent_pos
  by_cases h4 : 4 ≤ r
  · exact rankFour_B_of_four hv hpr hodd (by rw [hexp]; omega)
      (CarrierB.hasWitness_theta_four _ hodd (by omega))
  · exact rankFour_B_of_four hv hpr hodd (by rw [hexp]; omega)
      (CarrierB.hasWitness_bthree _ hodd (by omega))

theorem rankFour_B_even (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid) (hr : 4 ≤ r)
    (hp : q.p = 2) (hf : 2 ≤ q.exponent) [Finite (CFSGIndex.lie ⟨.B r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.B r q, hv⟩).Group := by
  obtain ⟨hchar, hord, -, hrank⟩ := typeB_mk_data r q hv
  rw [hp] at hchar hord
  have hq4 : 4 ≤ (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.fieldOrder := by
    rw [hord]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨s, hs, hs2, -, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf
  rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
  · refine rankFour_B_of_four hv hs hs2 (le_of_eq ?_)
      (CarrierB.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd) id id
        (CarrierB.det_full_ne_zero _ (by omega) hs hs2))
    rw [Fintype.card_fin, hrank]
  · exact rankFour_B_of_four hv hs hs2 (le_of_eq (Fintype.card_fin 4).symm)
      (CarrierB.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd)
        (fun c : Fin 4 => ⟨c, by omega⟩) (fun a : Fin 4 => ⟨a + 1, by omega⟩)
        (CarrierB.det_tri_ne_zero _ (by omega) hs))

theorem rankFour_B_two (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid) (hp : q.p = 2)
    (h5 : 5 ≤ r) [Finite (CFSGIndex.lie ⟨.B r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.B r q, hv⟩).Group := by
  obtain ⟨hchar, -, -, hrank⟩ := typeB_mk_data r q hv
  exact rankFour_B_of_four hv Nat.prime_three (by norm_num) le_rfl
    (CarrierB.hasWitness_short _ (hchar.trans hp) (by omega))

theorem rankFour_D_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid)
    (hp : q.p ≠ 2) [Finite (CFSGIndex.lie ⟨.D r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.D r q, hv⟩).Group := by
  obtain ⟨hchar, -, hexp, -⟩ := typeD_mk_data r q hv
  have hodd : (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.characteristic ≠ 2 := hchar ▸ hp
  have hf1 := q.exponent_pos
  exact rankFour_D_of_four hv (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.characteristic_prime
    hodd (by rw [hexp]; omega) (CarrierD.hasWitness_theta_four _ hodd)

theorem rankFour_D_even (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid)
    (hp : q.p = 2) (hf : 2 ≤ q.exponent) [Finite (CFSGIndex.lie ⟨.D r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.D r q, hv⟩).Group := by
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
  · refine rankFour_D_of_four hv hs hs2 (le_of_eq ?_)
      (CarrierD.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd) id id
        (CarrierD.det_full_ne_zero _ (hrank.trans h) hs hs2))
    rw [Fintype.card_fin, hrank, h]
  · exact rankFour_D_of_four hv hs hs2 (le_of_eq (Fintype.card_fin 4).symm)
      (CarrierD.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd)
        (fun c : Fin 4 => ⟨c, by omega⟩) (fun a : Fin 4 => ⟨a + 1, by omega⟩)
        (CarrierD.det_five_ne_zero _ (hrank.trans h) hs hs2))
  · exact rankFour_D_of_four hv hs hs2 (le_of_eq (Fintype.card_fin 4).symm)
      (CarrierD.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd)
        (fun c : Fin 4 => ⟨c, by omega⟩) (fun a : Fin 4 => ⟨a + 1, by omega⟩)
        (CarrierD.det_tri_ne_zero _ h hs))

theorem rankFour_D_two (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid) (hp : q.p = 2)
    (h5 : 5 ≤ r) [Finite (CFSGIndex.lie ⟨.D r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.D r q, hv⟩).Group := by
  obtain ⟨hchar, -, -, hrank⟩ := typeD_mk_data r q hv
  rcases (show r = 5 ∨ 6 ≤ r by omega) with h | h6
  · exact rankFour_D_of_four hv Nat.prime_three (by norm_num) le_rfl
      (CarrierD.hasWitness_five _ (hchar.trans hp) (by rw [hrank]; exact h))
  · exact rankFour_D_of_four hv Nat.prime_three (by norm_num) le_rfl
      (CarrierD.hasWitness_three _ (hchar.trans hp) (by rw [hrank]; exact h6))

theorem rankFour_twistedD_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid)
    (hp : q.p ≠ 2) [Finite (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group := by
  obtain ⟨hchar, -, hexp, -⟩ := typeTwistedD_mk_data r q hv
  have hodd : (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.characteristic ≠ 2 :=
    hchar ▸ hp
  have hf1 := q.exponent_pos
  exact rankFour_twistedD_of_four hv
    (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.characteristic_prime hodd
    (by rw [hexp]; omega) (CarrierTD.hasWitness_theta _ hodd)

theorem rankFour_twistedD_even (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (hp : q.p = 2) (hf : 2 ≤ q.exponent) (hr : 5 ≤ r)
    [Finite (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group := by
  obtain ⟨hchar, hord, -, hrank⟩ := typeTwistedD_mk_data r q hv
  rw [hp] at hchar hord
  have hq4 : 4 ≤ (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.fieldOrder := by
    rw [hord]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
  rcases (show r = 5 ∨ 6 ≤ r by omega) with h | h
  · obtain ⟨s, hs, hs2, -, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf
    exact rankFour_twistedD_of_four hv hs hs2 le_rfl
      (CarrierTD.hasWitness_torus_five _ hchar hq4 hs hs2 (hord ▸ hsd) (hrank.trans h))
  · obtain ⟨s, hs, hs2, hs5, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf
    exact rankFour_twistedD_of_four hv hs hs2 le_rfl
      (CarrierTD.hasWitness_torus_six _ hchar hq4 hs hs5 (hord ▸ hsd) h)

theorem rankFour_twistedD_five_two (q : PrimePower) (hv : (LieTypeIndex.twistedD 5 q).Valid)
    (hp : q.p = 2) (hf : q.exponent = 1) [Finite (CFSGIndex.lie ⟨.twistedD 5 q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.twistedD 5 q, hv⟩).Group := by
  obtain ⟨hchar, -, hexp, hrank⟩ := typeTwistedD_mk_data 5 q hv
  exact rankFour_twistedD_of_four hv Nat.prime_three (by norm_num) le_rfl
    (CarrierTD.hasWitness_tdfive _ (hchar.trans hp) (hexp.trans hf) hrank)

theorem rankFour_twistedD_two (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid)
    (hp : q.p = 2) (h6 : 6 ≤ r) [Finite (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group := by
  obtain ⟨hchar, -, -, hrank⟩ := typeTwistedD_mk_data r q hv
  exact rankFour_twistedD_of_four hv Nat.prime_three (by norm_num) le_rfl
    (CarrierTD.hasWitness_twShort _ (hchar.trans hp) (by rw [hrank]; exact h6))

theorem spinRankFour : Census3.SpinRankFour where
  typeB := fun r q hv hr h3 h4 [Finite (CFSGIndex.lie ⟨.B r q, hv⟩).Group] => by
    have hf1 := q.exponent_pos
    by_cases hp : q.p = 2
    · by_cases hf : 2 ≤ q.exponent
      · exact rankFour_B_even r q hv (by omega) hp hf
      · have hf' : q.exponent = 1 := by omega
        exact rankFour_B_two r q hv hp (by omega)
    · exact rankFour_B_odd r q hv hr hp
  typeD := fun r q hv h4 [Finite (CFSGIndex.lie ⟨.D r q, hv⟩).Group] => by
    have hf1 := q.exponent_pos
    by_cases hp : q.p = 2
    · by_cases hf : 2 ≤ q.exponent
      · exact rankFour_D_even r q hv hp hf
      · have hf' : q.exponent = 1 := by omega
        have h4' : 4 ≤ r := TypeDDiagramLieIndex.four_le_rank
          (TypeDLieIndex.toTypeDDiagramLieIndex ⟨⟨.D r q, hv⟩, by simp⟩)
        exact rankFour_D_two r q hv hp (by omega)
    · exact rankFour_D_odd r q hv hp
  typeTwistedD := fun r q hv h4 [Finite (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group] => by
    have hf1 := q.exponent_pos
    have h4' : 4 ≤ r := CarrierTD.four_le ⟨⟨.twistedD r q, hv⟩, by simp⟩
    by_cases hp : q.p = 2
    · have hr5 : 5 ≤ r := by omega
      by_cases hf : 2 ≤ q.exponent
      · exact rankFour_twistedD_even r q hv hp hf hr5
      · have hf' : q.exponent = 1 := by omega
        rcases (show r = 5 ∨ 6 ≤ r by omega) with rfl | h6
        · exact rankFour_twistedD_five_two q hv hp hf'
        · exact rankFour_twistedD_two r q hv hp h6
    · exact rankFour_twistedD_odd r q hv hp

end CFSG.RankThree.PartOne.CTP
