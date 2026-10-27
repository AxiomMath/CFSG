module

public import CFSG.Quasithin.EmptyFaithful.S153GFinal
public import CFSG.Quasithin.EmptyFaithful.S153H32

public section

namespace CFSG.Quasithin

theorem countCentralizer_of_preamble32 (h : Input32Preamble) : CountCentralizer :=
  fun G _ _ T Mc M V₁ V₂ Yp I L t c _ =>
    (h G T Mc M V₁ V₂ Yp I L t c).2.2.le.trans inf_le_left

end CFSG.Quasithin
