module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.Quasithin.Vol2.F134Orders
public import CFSG.Quasithin.Vol2.F134Ree
public import CFSG.Quasithin.Vol2.F134Tits
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem three_dvd_card_alternatingGroup (n : ℕ) (hn : 3 ≤ n) :
    3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm,
      Fintype.card_fin]
  have h3 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  rw [← h] at h3
  exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3

theorem three_dvd_card_carrier
    {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) :
    3 ∣ Nat.card (NativeSporadic.Carrier s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show 3 ∣ Nat.card NativeSporadic.M11
    rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num
  · show 3 ∣ Nat.card NativeSporadic.M12
    rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num
  · show 3 ∣ Nat.card NativeSporadic.M22
    rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num
  · show 3 ∣ Nat.card NativeSporadic.M23
    rw [CFSG.Sporadic.Schreier.m23_card]; norm_num
  · show 3 ∣ Nat.card NativeSporadic.M24
    rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num
  · show 3 ∣ Nat.card NativeSporadic.J1
    rw [CFSG.Sporadic.J1.card_J1]; norm_num
  · show 3 ∣ Nat.card NativeSporadic.J2
    rw [CFSG.Sporadic.J2.card_J2]; norm_num
  · show 3 ∣ Nat.card NativeSporadic.J4
    rw [CFSG.Sporadic.J4.card_J4]; norm_num
  · show 3 ∣ Nat.card NativeSporadic.HS
    rw [CFSG.Sporadic.HS.card_HS]; norm_num
  · show 3 ∣ Nat.card NativeSporadic.He
    rw [CFSG.Sporadic.He.card_He]; norm_num
  · show 3 ∣ Nat.card NativeSporadic.Ru
    rw [CFSG.Sporadic.Ru.card_Ru]; norm_num

theorem simpleThreePrimeSuzukiFact :
    SimpleThreePrimeSuzukiFact := by
  intro S _ _ _ hL h3
  rcases hL with ⟨m, h5, -, ⟨e⟩⟩ | ⟨p, -, -, ⟨f, -, hm⟩ | hm | hm⟩ |
      ⟨⟨f, ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, -, hm⟩ | ⟨-, -, hm⟩⟩ |
        hm⟩ | ⟨m, hm4, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  · apply absurd _ h3
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_alternatingGroup m (by omega)
  · exact absurd (F134.three_dvd_card_of_statedPSL_two hm) h3
  · exact absurd (F134.three_dvd_card_of_statedPSL_three hm) h3
  · exact absurd (F134.three_dvd_card_of_statedPSU_three hm) h3
  · exact absurd (F134.three_dvd_card_of_statedPSL_two hm) h3
  · exact absurd (F134.three_dvd_card_of_statedPSL_three hm) h3
  · exact absurd (F134.three_dvd_card_of_statedPSU_three hm) h3
  · exact absurd (F134.three_dvd_card_of_statedPSp_two_two hm) h3
  · exact absurd (F134.three_dvd_card_of_g2_two hm) h3
  · exact absurd (F134.three_dvd_card_of_trialityD4_two hm) h3
  · exact absurd (F134.three_dvd_card_of_twistedF4 hm) h3
  · exact ⟨f, hm⟩
  · exact absurd (F134.three_dvd_card_of_tits hm) h3
  · exact absurd (F134.three_dvd_card_of_statedPSL_four_five hm4 hm) h3
  · apply absurd _ h3
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_carrier hs

end CFSG.Quasithin.H13
