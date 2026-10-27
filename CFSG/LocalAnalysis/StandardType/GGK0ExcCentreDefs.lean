module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587

@[expose] def posNodes {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    Finset (Fin ρ.row.diagram.marks.length) :=
  Finset.univ.filter fun i => 0 < ρ.row.s.getD i.val 0

end CFSG.StandardType.GGK0ExcCentreU

end
