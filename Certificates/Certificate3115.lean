module

public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Certificates.Kernel.Spor.Co2ShapeSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG.KS.Co2Shape CFSG.Sporadic.Co2Cert

set_option maxRecDepth 100000 in
theorem co2ShapeK_rec : co2ShapeK co2Rec = true := by quickRfl

set_option maxRecDepth 100000 in
theorem co2Rec_group : co2Rec.group = "Co2" := by
  delta co2Rec co2RecLit
  rfl

open CFSG.Sporadic.Co2Cert in
theorem certificate3115 : co2ShapeOK = true :=
  co2ShapeOK_eq.trans (co2ShapeK_sound co2Rec_group co2ShapeK_rec)

end Certificates
