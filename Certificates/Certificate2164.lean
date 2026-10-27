module

public import CFSG.Sporadic.Schreier.J1CertCheckInputs
public import CFSG.Certificates.Kernel.Spor.J1ShapeSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG.KS.J1Shape CFSG.Sporadic.Schreier

set_option maxRecDepth 100000 in
theorem j1ShapeK_rec : j1ShapeK J1Certificate = true := by quickRfl

set_option maxRecDepth 100000 in
theorem j1Certificate_group : J1Certificate.group = "J1" := by
  delta J1Certificate j1CertLit
  rfl

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier in
theorem certificate2164 : J1Certificate.shapeOK = true :=
  j1ShapeK_sound j1Certificate_group j1ShapeK_rec

end Certificates
