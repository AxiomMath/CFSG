module

public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeBEven
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeDEven
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeTD
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessBThree
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessDTheta
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTDFour

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem four_le_e_of_hasWitness {d : ValidLieTypeIndex} {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 4 ≤ k) (h : HasWitness d.Group p k) [hfin : Finite (CFSGIndex.lie d).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie d).Group := by
  have : Finite d.Group := hfin
  exact CFSG.RankThree.PartOne.Census3.four_le_twoLocalOddRank_of_localRank hp hp2
    (hk.trans (le_localRank_of_hasWitness hp h))

theorem le_localRank_of_hasWitness' {d : ValidLieTypeIndex} {p k : ℕ} (hp : p.Prime)
    (h : HasWitness d.Group p k) [hfin : Finite (CFSGIndex.lie d).Group] :
    k ≤ localRank p (CFSGIndex.lie d).Group := by
  have : Finite d.Group := hfin
  exact le_localRank_of_hasWitness hp h

theorem spinRankFour_typeB (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid) (hr : 3 ≤ r) (h3 : ¬ (r = 3 ∧ q.p = 2))
    (h42 : ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1)) [Finite (CFSGIndex.lie ⟨.B r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.B r q, hv⟩).Group := by
  obtain ⟨hchar, hord, hexp, hrank⟩ := typeB_mk_data r q hv
  have hf1 := q.exponent_pos
  have hpr := (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.characteristic_prime
  by_cases hp : q.p = 2
  · rw [hp] at hchar hord
    by_cases hf : 2 ≤ q.exponent
    · have hq4 : 4 ≤ (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.fieldOrder := by
        rw [hord]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
      obtain ⟨s, hs, hs2, -, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf
      rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
      · refine four_le_e_of_hasWitness hs hs2 (le_of_eq ?_)
          (CarrierB.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd) id id
            (CarrierB.det_full_ne_zero _ (by omega) hs hs2))
        rw [Fintype.card_fin, hrank]
      · exact four_le_e_of_hasWitness hs hs2 (le_of_eq (Fintype.card_fin 4).symm)
          (CarrierB.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd)
            (fun c : Fin 4 => ⟨c, by omega⟩) (fun a : Fin 4 => ⟨a + 1, by omega⟩)
            (CarrierB.det_tri_ne_zero _ (by omega) hs))
    · have hf' : q.exponent = 1 := by omega
      exact four_le_e_of_hasWitness Nat.prime_three (by norm_num) le_rfl
        (CarrierB.hasWitness_short _ hchar (by omega))
  · have hodd : (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.characteristic ≠ 2 := hchar ▸ hp
    by_cases h4 : 4 ≤ r
    · exact four_le_e_of_hasWitness hpr hodd (by rw [hexp]; omega)
        (CarrierB.hasWitness_theta_four _ hodd (by omega))
    · exact four_le_e_of_hasWitness hpr hodd (by rw [hexp]; omega)
        (CarrierB.hasWitness_bthree _ hodd (by omega))

theorem spinRankFour_typeD (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) (h42 : ¬ (r = 4 ∧ q.p = 2 ∧ q.exponent = 1))
    [Finite (CFSGIndex.lie ⟨.D r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.D r q, hv⟩).Group := by
  obtain ⟨hchar, hord, hexp, hrank⟩ := typeD_mk_data r q hv
  have hf1 := q.exponent_pos
  have h4 : 4 ≤ r := TypeDDiagramLieIndex.four_le_rank
    (TypeDLieIndex.toTypeDDiagramLieIndex ⟨⟨.D r q, hv⟩, by simp⟩)
  by_cases hp : q.p = 2
  · rw [hp] at hchar hord
    by_cases hf : 2 ≤ q.exponent
    · have hq4 : 4 ≤ (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.fieldOrder := by
        rw [hord]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
      obtain ⟨s, hs, hs2, -, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf
      rcases (show r = 4 ∨ r = 5 ∨ 6 ≤ r by omega) with h | h | h
      · refine four_le_e_of_hasWitness hs hs2 (le_of_eq ?_)
          (CarrierD.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd) id id
            (CarrierD.det_full_ne_zero _ (hrank.trans h) hs hs2))
        rw [Fintype.card_fin, hrank, h]
      · exact four_le_e_of_hasWitness hs hs2 (le_of_eq (Fintype.card_fin 4).symm)
          (CarrierD.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd)
            (fun c : Fin 4 => ⟨c, by omega⟩) (fun a : Fin 4 => ⟨a + 1, by omega⟩)
            (CarrierD.det_five_ne_zero _ (hrank.trans h) hs hs2))
      · exact four_le_e_of_hasWitness hs hs2 (le_of_eq (Fintype.card_fin 4).symm)
          (CarrierD.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd)
            (fun c : Fin 4 => ⟨c, by omega⟩) (fun a : Fin 4 => ⟨a + 1, by omega⟩)
            (CarrierD.det_tri_ne_zero _ h hs))
    · have hf' : q.exponent = 1 := by omega
      rcases (show r = 4 ∨ r = 5 ∨ 6 ≤ r by omega) with rfl | h5 | h6
      · exact absurd ⟨rfl, hp, hf'⟩ h42
      · exact four_le_e_of_hasWitness Nat.prime_three (by norm_num) le_rfl
          (CarrierD.hasWitness_five _ hchar (by rw [hrank]; exact h5))
      · exact four_le_e_of_hasWitness Nat.prime_three (by norm_num) le_rfl
          (CarrierD.hasWitness_three _ hchar (by rw [hrank]; exact h6))
  · have hodd : (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.characteristic ≠ 2 := hchar ▸ hp
    exact four_le_e_of_hasWitness
      (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.characteristic_prime hodd
      (by rw [hexp]; omega) (CarrierD.hasWitness_theta_four _ hodd)

theorem spinRankFour_typeTwistedD (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (h42 : ¬ (r = 4 ∧ q.p = 2))
    [Finite (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group := by
  obtain ⟨hchar, hord, hexp, hrank⟩ := typeTwistedD_mk_data r q hv
  have hf1 := q.exponent_pos
  have h4 : 4 ≤ r := CarrierTD.four_le ⟨⟨.twistedD r q, hv⟩, by simp⟩
  by_cases hp : q.p = 2
  · rw [hp] at hchar hord
    have h5 : 5 ≤ r := by
      by_contra h
      exact h42 ⟨by omega, hp⟩
    by_cases hf : 2 ≤ q.exponent
    · have hq4 : 4 ≤ (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.fieldOrder := by
        rw [hord]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
      rcases (show r = 5 ∨ 6 ≤ r by omega) with h | h
      · obtain ⟨s, hs, hs2, -, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf
        exact four_le_e_of_hasWitness hs hs2 le_rfl
          (CarrierTD.hasWitness_torus_five _ hchar hq4 hs hs2 (hord ▸ hsd) (hrank.trans h))
      · obtain ⟨s, hs, hs2, hs5, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf
        exact four_le_e_of_hasWitness hs hs2 le_rfl
          (CarrierTD.hasWitness_torus_six _ hchar hq4 hs hs5 (hord ▸ hsd) h)
    · have hf' : q.exponent = 1 := by omega
      rcases (show r = 5 ∨ 6 ≤ r by omega) with rfl | h6
      · exact four_le_e_of_hasWitness Nat.prime_three (by norm_num) le_rfl
          (CarrierTD.hasWitness_tdfive _ hchar (hexp.trans hf') hrank)
      · exact four_le_e_of_hasWitness Nat.prime_three (by norm_num) le_rfl
          (CarrierTD.hasWitness_twShort _ hchar (by rw [hrank]; exact h6))
  · have hodd : (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.characteristic ≠ 2 :=
      hchar ▸ hp
    exact four_le_e_of_hasWitness
      (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.characteristic_prime hodd
      (by rw [hexp]; omega) (CarrierTD.hasWitness_theta _ hodd)

theorem le_localRank_B {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.B r q).Valid) {p k : ℕ}
    (hp : p.Prime) (h : HasWitness (TypeBLieIndex.Group ⟨⟨.B r q, hv⟩, trivial⟩) p k)
    [Finite (CFSGIndex.lie ⟨.B r q, hv⟩).Group] :
    k ≤ localRank p (CFSGIndex.lie ⟨.B r q, hv⟩).Group :=
  le_localRank_of_hasWitness' (d := ⟨.B r q, hv⟩) hp h

theorem le_localRank_twistedD {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedD r q).Valid)
    {p k : ℕ} (hp : p.Prime)
    (h : HasWitness (TypeTwistedDLieIndex.Group ⟨⟨.twistedD r q, hv⟩, by simp⟩) p k)
    [Finite (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group] :
    k ≤ localRank p (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group :=
  le_localRank_of_hasWitness' (d := ⟨.twistedD r q, hv⟩) hp h

theorem spinLarge_typeB3 (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid) (hp : q.p = 2)
    (hf : 3 ≤ q.exponent) [Finite (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group] :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ 3 ≤ localRank r (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group := by
  obtain ⟨hchar, hord, -, hrank⟩ := typeB_mk_data 3 q hv
  rw [hp] at hchar hord
  have hq4 : 4 ≤ (⟨⟨.B 3 q, hv⟩, trivial⟩ : TypeBLieIndex).1.fieldOrder := by
    rw [hord]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_sub_one hf
  refine ⟨s, hs, by omega, le_trans (le_of_eq ?_) (le_localRank_B hv hs
    (CarrierB.hasWitness_torus _ hchar hq4 hs (hord ▸ hsd) id id
      (CarrierB.det_full_ne_zero _ (by omega) hs (by omega))))⟩
  rw [Fintype.card_fin, hrank]

theorem spinLarge_twistedD4 (q : PrimePower) (hv : (LieTypeIndex.twistedD 4 q).Valid)
    (hp : q.p = 2) (hf : 2 ≤ q.exponent) [Finite (CFSGIndex.lie ⟨.twistedD 4 q, hv⟩).Group] :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ 3 ≤ localRank r (CFSGIndex.lie ⟨.twistedD 4 q, hv⟩).Group := by
  obtain ⟨hchar, hord, hexp, hrank⟩ := typeTwistedD_mk_data 4 q hv
  by_cases hf2 : q.exponent = 2
  · exact ⟨5, Nat.prime_five, by norm_num, le_localRank_twistedD hv Nat.prime_five
      (CarrierTD.hasWitness_tdfour _ (hchar.trans hp) (hexp.trans hf2))⟩
  rw [hp] at hchar hord
  have hq4 : 4 ≤ (⟨⟨.twistedD 4 q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.fieldOrder := by
    rw [hord]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_sub_one (show 3 ≤ q.exponent by
    omega)
  exact ⟨s, hs, by omega, le_localRank_twistedD hv hs
    (CarrierTD.hasWitness_torus_four _ hchar hq4 hs (by omega) (hord ▸ hsd) hrank)⟩

end CFSG.RankThree.PartTwo.Census.Spin
