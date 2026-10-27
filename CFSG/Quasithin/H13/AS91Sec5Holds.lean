module

public import CFSG.Quasithin.H13.AS91Sec5HM22
public import CFSG.Quasithin.H13.AS91Sec5TwoCQ
public import CFSG.Quasithin.H13.AS91Sec5Max13

public section

namespace CFSG.Quasithin.H13.AS91

theorem stmt5_2c_holds :
    Stmt5_2c := by
  intro G _ _ z hJ c y _ hyx g hg hgy
  have hgx : g • c.x0 ≠ c.x0 := hgy ▸ hyx
  obtain ⟨N, π, -, -, -, -, hker, hcomm, hodd⟩ :=
    Loc41.exists_linear_M22 hJ c.toLoc48.toLoc47.toLoc46.toLoc45.toLoc43.toLoc42.toLoc41
  exact c.conj_inf_E_eq_Z_of_le_Q hg hgx (c.conj_inf_E_le_Q N π hker hcomm hodd hg hgx)

theorem stmt5_max13_holds :
    Stmt5_Max13 :=
  stmt5_max13_of_linear fun _ _ _ _ hJ d => by
    obtain ⟨N, π, hNH, hQXN, hidx, hsurj, hker, -, -⟩ := Loc41.exists_linear_M22 hJ d
    exact ⟨N, π, hNH, hQXN, hidx, hsurj, hker⟩

end CFSG.Quasithin.H13.AS91
