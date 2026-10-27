module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4FinalTop
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48D3Final
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocProps
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Clause
public import CFSG.Quasithin.Vol2.GoldschmidtF431D3Props

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

section Holds


theorem f431D4_holds : F431D4 :=
  f431D4_of_inputs (fun hs => d4F424 hs) (d4_nonFusion d4ZH d4TH rfl rfl)
    (d4_localCent d4ZH d4TH rfl rfl) fun hD' hs =>
      have hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index := by
        rw [d4_conj_index hD']
        decide
      d3_clause_of_inputs hD' hs (fun _ hx => centralizer_d4U hs hx) (d3F424_of_simple hD' hs)
        (d3_nonFusion hs (fun _ hx => centralizer_d4U hs hx) hodd d3ZH d3TH rfl rfl)
        (d3_localCent hs (fun _ hx => centralizer_d4U hs hx) hodd (d4_card_aut_dvd hD') d3ZH d3TH
          rfl rfl)

end Holds

end CFSG.Quasithin.D4Hex
