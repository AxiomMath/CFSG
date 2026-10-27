module

public import CFSG.Quasithin.Recognition.SzVBEvenSetting
public import CFSG.Quasithin.Recognition.SzVBMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem f112R1c_holds : F112R1cStatementLegacyBare := by
  intro G _ _ K1 L2 S Zs h hB h2 h3
  have hRO : RankOneListedFacts.{0} := rankOneListedFacts
  obtain ⟨n, hn, hX⟩ := hB
  by_cases hab : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥
  · exact SzVB.vBeta_nonabelian_of_bender hRO h
      (fun hne => SzVB.benderLocalFacts_of_setting hRO h hn hX hne)
      (fun hL _ _ => (h2 hL).elim)
      (fun hab' => SzVB.even_critDist_false_of_setting hRO h hn hX h2 hab') hab
  · rcases Background.Harris.R1.nonab_holds G K1 L2 S Zs h ⟨n, hn, hX⟩ hab with h' | h'
    · exact h2 h'
    · exact h3 h'

end CFSG.Quasithin
