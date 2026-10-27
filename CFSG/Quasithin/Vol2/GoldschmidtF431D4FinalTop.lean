module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4FinalExt
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Simple
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4ExtMap

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Quasithin.H13.F431

section Assembly


theorem f431D4_of_inputs (hF424 : IsSimpleGroup D → D4F424) (hNF : D4NonFusion d4ZH d4TH)
    (hLoc : D4LocalCent d4ZH d4TH)
    (hD3 : ∀ {D' : Type} [Group D'], IsLieOverTwo .trialityD4 0 1 D' → IsSimpleGroup D →
      D3ClauseVacuous) : F431D4 := by
  rintro G _ _ hG - M₁ M₂ z ⟨D₁, _, hD₁, hext⟩ hz2 hz1 hzr hzc hcent
  obtain ⟨E⟩ := isExtensionOfLieAmalgam_iff.1 hext
  obtain ⟨e₀⟩ := nonempty_equiv_trialityGroup8 D₁ hD₁
  have hs : IsSimpleGroup D := d4_isSimpleGroup hD₁
  obtain ⟨hcard, hZ⟩ := d4_card_aut hD₁
  have hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index := by
    rw [d4_conj_index hD₁]
    decide
  obtain ⟨x, -, hP⟩ := d4_yamalgam_classify hs (E.congr e₀).yam
  rcases hP with ⟨hP1, hP2⟩ | ⟨hP1, hP2⟩
  · rcases d4_aut_intermediate hD₁ ((E.congr e₀).conjSylow x).Mbar
        ((E.congr e₀).conjSylow x).inn_le with hM | hM
    · obtain ⟨χ⟩ := d4_case_inn hs (hF424 hs) hNF hLoc ((E.congr e₀).conjSylow x) hM hP1 hP2 hZ
        hodd hzr hzc hz2 hz1 hcent
      exact ⟨D₁, inferInstance, hD₁, ⟨χ.trans e₀.symm⟩⟩
    · exact (d4_case_top hs (hD3 hD₁ hs) hG ((E.congr e₀).conjSylow x) hM hP1 hP2 hZ hodd hzr hzc
        hz2 hz1 hcent).elim
  · exfalso
    have hP1' : ((E.congr e₀).conjSylow x).P1 = d4N := hP1
    obtain ⟨n, -, hn1, -, -, hnc⟩ := ((E.congr e₀).conjSylow x).exists_zero_data_inn hZ hodd hzr
      hzc hz2 hz1
    exact d4_swap_false hs hn1 (fun s hs' hk => hnc s (by rw [hP1']; exact hs') hk)

end Assembly

end CFSG.Quasithin.D4Hex
