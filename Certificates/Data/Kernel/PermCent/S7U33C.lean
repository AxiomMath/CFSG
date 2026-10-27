module

public import Certificates.Data.Kernel.PermCent.CV
public import Certificates.Data.S7U33

public section

namespace CFSG.Certificates.Kernel.PkCV.S7U33C

open CFSG.GH74.KGroups

@[expose] noncomputable def gensC : List (CV 28) :=
  [cOf U33.pa, cOf U33.pb, cOf U33.sg0, (cOf U33.pa)⁻¹, (cOf U33.pb)⁻¹, (cOf U33.sg0)⁻¹]

@[expose] noncomputable def wAC (w : List ℕ) : CV 28 := (w.map fun k => gensC.getD k 1).prod

@[expose] noncomputable def I1 : CV 28 := wAC [1, 3, 2, 1, 2, 0]

@[expose] noncomputable def J1 : CV 28 := wAC [2, 3, 2, 1]

@[expose] noncomputable def I2 : CV 28 := wAC [1, 2, 2, 3, 5, 4]

@[expose] noncomputable def J2 : CV 28 := wAC [3, 4, 5, 0, 1, 0]

@[expose] noncomputable def SG : CV 28 := cOf U33.sg0

@[expose] noncomputable def PA : CV 28 := cOf U33.pa

@[expose] noncomputable def PB : CV 28 := cOf U33.pb

@[expose] noncomputable def SC : List (CV 28) := elemsC Certificates.S5RowsU33.QSA

@[expose] noncomputable def AC : List (CV 28) := elemsC U33.QA

@[expose] noncomputable def CZC : List (CV 28) :=
  AC.filter fun x => eq22C x (I1 * I1) (I1 * I1) x

@[expose] noncomputable def FPa : List (CV 28) :=
  [wAC [0, 1, 3], SG, wAC [0, 1, 3], SG⁻¹, wAC [1, 2, 0, 1, 0], wAC [2, 2], wAC [1, 2, 0, 1, 0],
    SG⁻¹, wAC [1, 2, 0, 1, 0]]

@[expose] noncomputable def FPb : List (CV 28) :=
  [SG⁻¹, wAC [0, 1, 3], wAC [0, 1, 3], SG⁻¹, wAC [0, 1, 3], SG, wAC [0, 1, 3], SG]

end CFSG.Certificates.Kernel.PkCV.S7U33C

end
