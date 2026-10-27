module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsPassDefs

public section

namespace CFSG.Certificates.Kernel.PkCV.L33T

open CFSG.GH74.KGroups.L33 CFSG.OddStandard.SmallF3.L33

@[expose] noncomputable def innerC (g : CV 26) : Bool :=
  decide (g * g = 1) && !decide (g = 1) && siftC QP g 0

@[expose] noncomputable def outerC (g : CV 26) : Bool := decide (g * g = 1) && !siftC QP g 0

@[expose] noncomputable def centKC (g : CV 26) : Bool := decide (g * cOf kTab = cOf kTab * g)

@[expose] noncomputable def centPC (g : CV 26) : Bool :=
  decide (g * cOf kTab = cOf kTab * g) && siftC QP g 0

@[expose] def e1L : List (Equiv.Perm (Fin 26)) :=
  [1, zTab, yTab, CFSG.Sporadic.Schreier.tab (modelZ * modelY), kTab, zkTab,
    CFSG.Sporadic.Schreier.tab (modelY * modelK),
    CFSG.Sporadic.Schreier.tab (modelZ * modelY * modelK)]

@[expose] def e2L : List (Equiv.Perm (Fin 26)) :=
  [1, zTab, wTab, CFSG.Sporadic.Schreier.tab (modelZ * (modelX ^ 2 * modelY)), kTab, zkTab,
    CFSG.Sporadic.Schreier.tab ((modelX ^ 2 * modelY) * modelK),
    CFSG.Sporadic.Schreier.tab (modelZ * (modelX ^ 2 * modelY) * modelK)]

@[expose] noncomputable def norm1C (n : CV 26) : Bool :=
  !([zTab, yTab, kTab].all fun e => decide (n * cOf e * n⁻¹ ∈ e1L.map cOf)) ||
    decide (n * cOf kTab * n⁻¹ = cOf kTab)

@[expose] noncomputable def norm2C (n : CV 26) : Bool :=
  !([zTab, wTab, kTab].all fun e => decide (n * cOf e * n⁻¹ ∈ e2L.map cOf)) ||
    decide (n * cOf zkTab * n⁻¹ = cOf zkTab)

end CFSG.Certificates.Kernel.PkCV.L33T

end
