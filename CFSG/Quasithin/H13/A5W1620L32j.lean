module

public import CFSG.Quasithin.H13.A5W1620L32i
public import CFSG.Quasithin.H13.A5W1620Red

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Quasithin

theorem lemma13620L32Red (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) : Lemma13620L32Red := by
  intro G _ _ T L V S hS K _ hK hT ⟨F, _, _, hF2, ⟨e⟩⟩ K₀ hK₀K hK₀ hTK₀ hK₀W hz hchar _ hWP hred
    hLvK₀ h1317 ⟨F', _, _, α, hF'2, hα⟩ ⟨i, hi⟩
  exact S.Lv_le_of_red h1222 h517 hS.hF hK hT hF2 e hK₀K hK₀ hTK₀ hK₀W hz hchar hWP hred hLvK₀
    h1317 hF'2 hα hi

end CFSG.Quasithin.H13.A5
