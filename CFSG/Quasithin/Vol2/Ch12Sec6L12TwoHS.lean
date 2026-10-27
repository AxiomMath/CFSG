module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeaves
public import CFSG.Quasithin.H13.LocDblRankHS

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint

theorem a6LocHS_holds :
    A6LocHS := by
  intro X _ _ ⟨e⟩ Y F h
  have hF : IsElemAbelian 2 F := h.2.2.2.1
  haveI : Finite NativeSporadic.HS := Finite.of_equiv X e.toEquiv
  have hb : CFSG.Quasithin.H13.LocDbl.ElemAbelianBound X 16 :=
    CFSG.Quasithin.H13.LocDbl.ElemAbelianBound.of_mulEquiv
      (A := NativeSporadic.HS) (A' := X) e.symm
      CFSG.Quasithin.H13.LocDbl.elemAbelianBound_HS
  exact hb F hF

end CFSG.Quasithin.H13.K1262Two
