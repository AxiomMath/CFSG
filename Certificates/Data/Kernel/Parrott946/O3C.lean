
module

public import Certificates.Data.Kernel.PermCent.CV
public import Certificates.Data.ParrottPSp43
public import Certificates.Certificate946016Base

public section

namespace CFSG.KC.Parrott946

open CFSG.Certificates.Kernel.PkCV CFSG.RankThree.GF2n.Parrott

@[expose] noncomputable def closeStepC (S steps : List (CV 45)) : List (CV 45) :=
  (S ++ (S.product steps).map (fun p => p.1 * p.2)).eraseDups

@[expose] noncomputable def closeFuelC (steps : List (CV 45)) : Nat → List (CV 45) → List (CV 45)
  | 0, S => S
  | n + 1, S => closeFuelC steps n (closeStepC S steps)

@[expose] noncomputable def o3StepsC : List (CV 45) := o3Steps.map cOf

@[expose] noncomputable def O3C : List (CV 45) := closeFuelC o3StepsC 6 [1]

end CFSG.KC.Parrott946

end
