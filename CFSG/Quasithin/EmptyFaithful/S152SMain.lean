module

public import CFSG.Quasithin.EmptyFaithful.S152SOrd
public import CFSG.Quasithin.EmptyFaithful.S152SL32
public import CFSG.Quasithin.EmptyFaithful.S152SShape

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

section Main


theorem insp15224NoF2_of_borel (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G)
    (hBQ : BigQBorelCentralizerTrivial) (hD : NotLieCharTwoAlt7) (hF : NotLieCharTwoSporadic) :
    Insp15224NoF2 := by
  intro G _ _ I S Mi L L₀ P z hSQ hO hS hzS hzC hz2 hz1 hMi hMiI hmax hcomp hLnot hLz hcases hlie
    hnC hnA hF2 hL₀ hL₀n hI hPM hP3 hP9 hPexp
  obtain ⟨hinn, hbt | ⟨hcen, hl32⟩⟩ := typeAnalysis hBQ hD hF hcomp hcases hlie hnC hnA hF2
  · exact S152S.false_of_borel_shape (hA3 G) hSQ hS hzC hz2 hMi hmax hcomp hLz hinn hL₀ hL₀n hbt
  · exact S152S.false_of_l32 (hA3 G) hSQ hS hz2 hMi hcomp hLz hinn hl32 hcen hPM hP9 hPexp

end Main

section MainBigQ


theorem insp15224NoF2_of_bigQ (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G)
    (hBQ : BigQBorelCentralizerTrivial) : Insp15224NoF2 :=
  insp15224NoF2_of_borel hA3 hBQ S152S.notLieCharTwoAlt7 S152S.notLieCharTwoSporadic

end MainBigQ

end CFSG.Quasithin
