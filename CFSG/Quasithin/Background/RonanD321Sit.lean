module

public import CFSG.Quasithin.Background.SmithD321CaseI
public import CFSG.Quasithin.Background.SmithD321Main
public import CFSG.Quasithin.Background.SmithD39TwoSzHolds
public import CFSG.Quasithin.Vol2.Ch5Sec1L34DiscList

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD391 CFSG.Open
  CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W]

theorem exists_caseIIa
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (hB : D321Base M Mp T L V t) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (htop : orbSup T V ≠ ⊤) (h3L : 3 ∣ Nat.card ↥L) :
    ∃ A r, D321Sit M Mp T L V t A r ∧
      A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ ∧ V < orbSup T V ∧
      ((D36cConcl Mp T L V t ∧ commSub (orbSup T V) L = V) ∨
        (D36cConcl Mp T (conjAutSub t L) V t⁻¹ ∧
          commSub (orbSup T V) (conjAutSub t L) = V)) := by
  obtain ⟨A, r, hS⟩ := hB.exists_sit hqM htop
  have hAC := hS.inf_cent_eq_bot_of_three_dvd SmithD39Two.d38Top_holds a23SQTKListFact
    H13.simpleThreePrimeSuzukiFact h3L
  have hlt : V < orbSup T V := by
    rcases (le_orbSup T V).eq_or_lt with hVT | hlt
    · exact (caseI_false asB56_holds d37_holds hS hVT hAC).elim
    · exact hlt
  refine ⟨A, r, hS, hAC, hlt, ?_⟩
  rcases SmithD39Two.d36c_holds W M Mp T L V hB.hD hlt t hB.htT hB.htn hB.hMp with hc | hc
  · left
    refine ⟨hc, ?_⟩
    by_contra hne
    exact caseIIb_false hS hc hne hAC
  · right
    refine ⟨hc, ?_⟩
    by_contra hne
    exact caseIIb_false hS.swap hc hne hAC

end CFSG.Quasithin.RonanD321
