module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsTN3
public import CFSG.Quasithin.Vol2.Ch9Sec3TNNQ

public section

namespace CFSG.Quasithin.H13.Ch9

theorem a314ThreeNormRest3_of (h36 : A36ForSQTK) : A314ThreeNormRest3 := by
  intro Y _ _ hY h3 T B L D hT hB hA5 hL hBL _ hLn hD3 hDab hDT hDL hb hTB hD3e hcase
  obtain ⟨b, ⟨hbB, hbD⟩, hb3, -⟩ := hb
  exact TN.le_normalizer_of_nq h36 hY h3 hT hB hA5 hL hBL hLn hD3 hDab hDT hDL hTB hD3e hcase
    hbB hbD hb3

end CFSG.Quasithin.H13.Ch9
