module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocalMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocStdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocOrientMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdLocMain

public section

namespace CFSG.Quasithin.H13.F431.D4q.Local

open CFSG.Quasithin.H13.F431.D4q.Struct


theorem std3D4_holds (f : ℕ) (hf : 2 ≤ f) : Std3D4 f := by
  intro K _ _ _ σ hK hσ
  have hσ3 := sigma_cube σ hK hσ
  obtain ⟨V, L, hL⟩ := StdLoc.stdLoc_d4 σ hσ3 hf hK hσ
  exact ⟨V, L, Loc.ZC σ, Loc.QC σ, Loc.XC σ, Loc.YC σ, Loc.tC σ hσ3, Loc.nrC σ, Loc.naC σ,
    2 ^ f, 4, Loc.stdTwo_d4 σ hσ3 (by omega) hK hσ, hL,
    Loc.stdOrient_d4 σ hσ3 (by omega) hK hσ⟩

end CFSG.Quasithin.H13.F431.D4q.Local
