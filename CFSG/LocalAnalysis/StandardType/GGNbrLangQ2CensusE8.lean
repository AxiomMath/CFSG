module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcField
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusE8Rank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem q2c_rLevel_E8 :
    Q2CensusRLevel (fun lab => lab.tag = .E8) (fun kind => kind = .e8Three) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  have hall := largeEvenLabelAll_and (q2c_E8_rank hS hp hp2 hsplit hpd)
    (q2c_exc_field_E8 (d := d) hS hp hp2 hm)
  refine largeEvenRawDatum_mono ?_ (hall Q hQ)
  rintro R _ I F ⟨hq, hrank, hfield⟩
  refine ⟨hq, fun A hA hAI hbig _ hlo hup u hu huo J hJ _ _ K _ _ hK he => ?_⟩
  obtain ⟨hp3, hd9⟩ := hrank A hA hAI hbig hlo hup
  obtain ⟨s, hs1, hms, hsd⟩ := hfield (by omega) u (hAI u hu) huo J hJ K hK he
  have hs : s = 1 := by
    rw [hd9] at hsd
    norm_num at hsd
    omega
  subst hs
  refine ⟨.e8Three, rfl, hp, hp2, hpd, hpm, hS, hp3, hd9, ?_⟩
  rw [hms]
  simp

end CFSG.StandardType
