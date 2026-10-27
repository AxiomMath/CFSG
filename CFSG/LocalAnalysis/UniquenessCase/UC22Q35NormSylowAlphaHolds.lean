module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1Vac
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1SL4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1SL5
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1SD
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1Orth
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35Exc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kq35NormSylowAlpha_holds :
    KQ35NormSylowAlpha := by
  intro X _ _ _ t n p hp hadm hfun hX P x hx s m hs hs7 hm hsm
  obtain ⟨hs11, hs13⟩ := uc22s2112r34q35_ne_eleven_ne_thirteen hm hsm
  cases t
  case PSL =>
    obtain rfl | rfl := hfun
    · obtain rfl | rfl := hp
      · exact uc22s2112r34q35_alpha_psl4_three hX x hs hs7 hs13
      · exact uc22s2112r34q35_alpha_psl4_five hX P hx hs hs7
    · obtain rfl | rfl := hp
      · exact uc22s2112r34q35_alpha_psl5_three hX x hs hs7 hs11 hs13
      · exact uc22s2112r34q35_alpha_psl5_five hX P hx hs hs7
  case PSU =>
    obtain rfl | rfl := hfun
    · obtain rfl | rfl := hp
      · exact uc22s2112r34q35_alpha_psu4_three hX P hx hs hs7
      · exact uc22s2112r34q35_alpha_psu4_five hX P hx hs hs7 hs13
    · obtain rfl | rfl := hp
      · exact uc22s2112r34q35_alpha_psu5_three hX P hx hs hs7
      · exact uc22s2112r34q35_alpha_psu5_five hX P hx hs hs7 hs13
  case PSp =>
    obtain rfl := hfun
    obtain rfl | rfl := hp
    · exact uc22s2112r34q35_alpha_psp4_three hX x hs hs7
    · exact uc22s2112r34q35_alpha_psp4_five hX x hs hs7 hs13
  case POmegaOdd =>
    obtain rfl := hfun
    exact uc22s2112r34q35_alpha_omegaOdd hp hX P hx hs hs7 hs13
  case POmegaMinus =>
    obtain rfl := hfun
    exact uc22s2112r34q35_alpha_omegaMinus hp hX P hx hs hs7 hs13
  case G2 =>
    obtain ⟨hp', -, rfl, -⟩ := hadm
    intro hxs
    have hodd : Odd (orderOf x) := by
      rw [hxs]
      exact hs.odd_of_ne_two (by omega)
    have h3 : orderOf x ∣ 3 := by
      exact uc22s2112r34q35_normSylow_G2_of_odd hp' (by omega) hX P hx hodd
    have hle : s ≤ 3 := Nat.le_of_dvd (by norm_num) (by simpa [hxs] using h3)
    omega
  case trialityD4 =>
    obtain ⟨hp', -, rfl⟩ := hadm
    intro hxs
    have hodd : Odd (orderOf x) := by
      rw [hxs]
      exact hs.odd_of_ne_two (by omega)
    have h3 : orderOf x ∣ 3 := by
      exact uc22s2112r34q35_normSylow_D4_of_odd hp' (by omega) hX P hx hodd
    have hle : s ≤ 3 := Nat.le_of_dvd (by norm_num) (by simpa [hxs] using h3)
    omega
  case POmegaPlus => cases hfun
  case F4 => cases hfun
  case E6 => cases hfun
  case E7 => cases hfun
  case E8 => cases hfun
  case twistedE6 => cases hfun
  case twistedB2 => cases hfun
  case twistedG2 => cases hfun
  case twistedF4 => cases hfun
  case Tits => cases hfun

end CFSG.LocalAnalysis.UniquenessCase.UC22
