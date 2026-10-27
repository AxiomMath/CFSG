module

public import CFSG.Quasithin.EmptyFaithful.S153YSBlock
public import CFSG.Quasithin.EmptyFaithful.S153YSPort
public import CFSG.Quasithin.EmptyFaithful.S153UDef

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem inputC61S3_proved : InputC61S3 := by
  intro G _ _ I T T₀ h1 h2 h3 h4 h5 h6 h7 h8 h9
  have h : YS.S3Hyp I T T₀ := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨U, L, -, -, hmin, hcharU, hblk, hL3, hth, hUeq, hT₀N, hOV, hC52⟩ := h.exists_reduction
  rw [← hOV]
  exact YS.a3_single_O2 hmin hcharU hblk hL3 hth hUeq hT₀N h5 h6 hC52

end CFSG.Quasithin
