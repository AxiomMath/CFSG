module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.GH74.KGroups.L34AutInputs

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5168

open CFSG.GH74.KGroups.L34

@[expose] def a : Equiv.Perm (Fin 42) := sg1 * sg2 * PB * sg0 * PA

@[expose] def b : Equiv.Perm (Fin 42) := PA * sg1 * sg2 * PB * sg0

@[expose] noncomputable def gA : CV 42 := cOf sg1 * cOf sg2 * cOf PB * cOf sg0 * cOf PA

@[expose] noncomputable def gB : CV 42 := cOf PA * cOf sg1 * cOf sg2 * cOf PB * cOf sg0

@[expose] noncomputable def heisC (x y : CV 42) : Bool :=
  let z := x⁻¹ * y⁻¹ * x * y
  powOneC x 3 && powOneC y 3 && !eq22C x y y x && eq22C z x x z && eq22C z y y z && powOneC z 3

end CFSG.Certificates.Kernel.PkCV.KGrp.K5168
