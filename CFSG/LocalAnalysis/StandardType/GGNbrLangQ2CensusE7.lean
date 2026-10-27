module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcField
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusE7Rank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem q2c_rLevel_E7 :
    Q2CensusRLevel (fun lab => lab.tag = .E7) (fun kind => kind = .e7Seven) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  have hall := largeEvenLabelAll_and (q2c_E7_rank hS hp hp2 hsplit hpd)
    (q2c_exc_field_E7 (d := d) hS hp hp2 hm)
  refine largeEvenRawDatum_mono ?_ (hall Q hQ)
  rintro R _ I F ⟨hq, hrank, hfield⟩
  refine ⟨hq, fun A hA hAI hbig _ hlo hup u hu huo J hJ _ _ K _ _ hK he => ?_⟩
  have hcase := hrank A hA hAI hbig hlo hup
  have h7 : p = 7 ∧ d = 7 := by
    rcases hcase with h | ⟨hn1, hp3, hd6⟩
    · exact h
    · exfalso
      obtain ⟨s, hs1, hms, hsd⟩ := hfield (by omega) u (hAI u hu) huo J hJ K hK he
      rw [hn1] at hms
      rw [hd6] at hsd
      norm_num at hsd
      omega
  obtain ⟨hp7, hd7⟩ := h7
  obtain ⟨s, hs1, hms, hsd⟩ := hfield (by omega) u (hAI u hu) huo J hJ K hK he
  have hs : s = 1 := by
    rw [hd7] at hsd
    norm_num at hsd
    omega
  subst hs
  refine ⟨.e7Seven, rfl, hp, hp2, hpd, hpm, hS, hp7, hd7, ?_⟩
  rw [hms]
  simp

end CFSG.StandardType
