module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcField
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusE6Rank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem q2c_rLevel_E6 :
    Q2CensusRLevel (fun lab => lab.tag = .E6) (fun kind => kind = .e6Three) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  have hall := largeEvenLabelAll_and (q2c_E6_rank hS hp hp2 hsplit hpd)
    (q2c_exc_field_E6 (d := d) hS hp hp2 hm)
  refine largeEvenRawDatum_mono ?_ (hall Q hQ)
  rintro R _ I F ⟨hq, hrank, hfield⟩
  refine ⟨hq, fun A hA hAI hbig _ hlo hup u hu huo J hJ _ _ K _ _ hK he => ?_⟩
  have hcase := hrank A hA hAI hbig hlo hup
  have hd5 : 5 ≤ d := by rcases hcase with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  obtain ⟨s, hs1, hms, hsd, hd6⟩ := hfield hd5 u (hAI u hu) huo J hJ K hK he
  have h36 : p = 3 ∧ d = 6 := by
    rcases hcase with h | ⟨_, h⟩
    · exact h
    · omega
  obtain ⟨hp3, hd6'⟩ := h36
  have hs : s = 1 := by
    rw [hd6'] at hsd
    norm_num at hsd
    omega
  subst hs
  refine ⟨.e6Three, rfl, hp, hp2, hpd, hpm, hS, hp3, hd6', ?_⟩
  rw [hms]
  simp

end CFSG.StandardType
