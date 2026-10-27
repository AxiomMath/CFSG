module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteEightCases
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCount
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteSeven
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteGeoMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteRedMain

public section

namespace CFSG.Quasithin.Fan86.Tutte

theorem tutteCalculus : TutteCalculus := by
  intro H _ s r l ξ Hs h
  by_contra hs
  have h6 : 6 ≤ s := by omega
  rcases h.xi_case with h7 | h8
  · exact le_five_of_two_cores h6 (not_seven_case7 h h7)
      (fun k hk h3 => abel_of_le_two_thirds h hk h3)
      (fun i₁ i₂ h1 h12 h2 hab => no_two_cores7 h h7 i₁ i₂ h1 h12 h2 hab)
  · rcases Nat.even_or_odd s with he | ho
    · refine le_five_of_two_cores h6 ?_ (fun k hk h3 => abel_of_le_two_thirds h hk h3)
        (fun i₁ i₂ h1 h12 h2 hab => no_two_cores8 h h8 i₁ i₂ h1 h12 h2 hab)
      rintro rfl
      exact absurd he (by decide)
    · exact not_odd_case8 h h8 (by omega) ho

theorem tutte_regular : TutteRegular :=
  Geo.tutte_regular_of_calculus tutteCalculus

theorem tutteTree : TutteTree :=
  tutteTree_of_regular tutte_regular

end CFSG.Quasithin.Fan86.Tutte
