module

public import CFSG.Quasithin.Background.F918J0
public import CFSG.Quasithin.Background.F918K5
public import CFSG.Quasithin.Background.F918K6
public import CFSG.Quasithin.Background.F918K7

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.Vol2.Ch10.SecA

theorem insp5aNonShape_of_g2Two
    (hg2 : FactG2TwoNormal) : Insp5aNonShape := by
  intro V _ _ G L hB hA hns
  have hX := nsGroup_of_a38Types hA hns
  exact ⟨fun _ hAo => hX.not_b42Conclusion hg2 hB hns hAo, hX.not_asB45Table hns,
    hX.not_asB45Part3⟩

theorem insp5aNonShape_holds :
    Insp5aNonShape :=
  insp5aNonShape_of_g2Two factG2TwoNormal_holds

end CFSG.Quasithin
