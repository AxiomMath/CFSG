module

public import CFSG.Quasithin.EmptyFaithful.S1421QA28Defs
public import CFSG.Quasithin.Vol2.Ch10SecK2Tn
public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.Quasithin.H13.VolIA38Orders
public import CFSG.Quasithin.H13.ExcludedOrders

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint

namespace QA28

theorem two_pow_six_dvd_mul {n : ℕ} (hn : 6 ≤ n) (u : ℕ) : 2 ^ 6 ∣ 2 ^ n * u :=
  Dvd.dvd.mul_right (pow_dvd_pow 2 hn) u

theorem rank2TwoPart_holds :
    Rank2TwoPart := by
  intro X _ h
  rcases h with ⟨f, ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hodd, hf, h⟩⟩ | hT
  ·
    obtain ⟨u, -, hc, -⟩ := Vol2.Ch10.SecC.C10KH.card_of_isPSL3 hf h
    rcases Nat.lt_or_ge f 2 with h1 | h2
    · obtain rfl : f = 1 := by omega
      exact Or.inl (Ch1Four.card_of_isPSL_three_two h)
    · exact Or.inr (hc ▸ two_pow_six_dvd_mul (by omega) u)
  ·
    have hc := Vol2.Ch10.SecC.C10KH.card_of_isSL3 h
    rcases Nat.lt_or_ge f 2 with h1 | h2
    · obtain rfl : f = 1 := by omega
      left
      rw [hc]
      norm_num
    · exact Or.inr (hc ▸ two_pow_six_dvd_mul (by omega) _)
  ·
    have hc := Vol2.Ch10.SecC.C10KH.card_of_isPSp4 (by omega) h
    exact Or.inr (hc ▸ two_pow_six_dvd_mul (by omega) _)
  ·
    have hc := Vol2.Ch10.SecC.C10KH.card_of_isG2 h
    exact Or.inr (hc ▸ two_pow_six_dvd_mul (by omega) _)
  ·
    have hc : Nat.card X = ordTrialityD4 (2 ^ f) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
    obtain ⟨r, -, hr⟩ := Quasithin.H13.VolI.two_part_ordTrialityD4 hf
    exact Or.inr (by rw [hc, hr]; exact two_pow_six_dvd_mul (by omega) r)
  ·
    obtain ⟨k, hk, hc⟩ := Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel h
    obtain ⟨r, -, hr⟩ := Quasithin.H13.VolI.two_part_ordTwistedF4 (f := 2 * k + 1) (by omega)
    exact Or.inr (by rw [hc, hr]; exact two_pow_six_dvd_mul (by omega) r)
  ·
    have hc := CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hT
    right
    rw [hc]
    unfold ordTits
    norm_num

end QA28

end CFSG.Quasithin
