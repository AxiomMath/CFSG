module

public import CFSG.Quasithin.Recognition.F112RGold
public import CFSG.Quasithin.Recognition.CertR2aBridges
public import CFSG.Quasithin.Recognition.M12AmalClass
public import CFSG.Quasithin.Recognition.M12AmalAutFeit

public section

namespace CFSG.Quasithin

theorem r2aBridges
    : R2aBridges where
  g22 := g22_bridge
  g22Prime := g22Prime_bridge
  m12 := fun D _ _ H₁ H₂ h => m12_f6YBridge D H₁ H₂ h
  autM12 := fun D _ _ H₁ H₂ h => autM12_f6YBridge' D H₁ H₂ h

end CFSG.Quasithin
