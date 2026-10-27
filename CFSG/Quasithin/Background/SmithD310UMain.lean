module

public import CFSG.Quasithin.Background.SmithD310UCaseI
public import CFSG.Quasithin.Background.SmithD310UCount
public import CFSG.Quasithin.Background.SmithD39TwoClif

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.SmithD310U CFSG.Quasithin.SmithD39Two

theorem d310Unfaith_of_clif (h35 : D35) (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hClif : ClifStep) : D310Unfaith := by
  intro W _ _ M Mp T L V hD hMp hqM hlt hunf
  subst Mp
  by_contra htop
  obtain ⟨t, A, r, k, hS⟩ := d310USit_of h35 hD hqM hlt hunf htop
  obtain ⟨u', hu', s, hs, hu'3, hu'1, hs2, hsu⟩ := exists_inv_of_d35Five hS.h5
  rcases alpha_or_e9_of_d35Five hS.h5 with ⟨n, hn, hα⟩ |
      ⟨u, hu, w, hw, hu3, hw3, huw, hu1, hwu⟩
  · by_cases hAC : A ≤ Subgroup.centralizer (L : Set (MulAut W))
    · obtain ⟨g, hgL, hg4, hg2⟩ := exists_four_of_binaryNaturalSL3 hα
      exact caseI_false_of_clif h38 hA23 hSzF hClif hS hAC hu' hs hu'3 hu'1 hs2 hsu hgL hg4 hg2
    · exact caseII_false hS hn hα hAC
  · exact beta_false h38 hA23 hSzF hS hu hw hu3 hw3 huw hu1 hwu hu' hs hu'3 hu'1 hs2 hsu

theorem SmithD310U.clifStep_of (hA21 : AsA21SQTKSection) (hB42 : AsB42) : ClifStep := by
  intro Γ _ _ hΓ Q _ _ _ hQ K A hK hAK hAc hA2 Y hY hKY hAY hr
  exact exists_noncyclic_three_of_clif hA21 hB42 hΓ hQ hK hAK hAc hA2 hY hKY hAY hr

theorem d310Unfaith_of_inputs (h35 : D35) (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hA21 : AsA21SQTKSection) (hB42 : AsB42) :
    D310Unfaith :=
  d310Unfaith_of_clif h35 h38 hA23 hSzF (SmithD310U.clifStep_of hA21 hB42)

end CFSG.Quasithin
