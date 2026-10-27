module

public import CFSG.Quasithin.EmptyFaithful.S153GS0Max
public import CFSG.Quasithin.EmptyFaithful.S153GExists
public import CFSG.Quasithin.EmptyFaithful.S153GStrong

public section

namespace CFSG.Quasithin

theorem input15325Count_of_inputs (h113 : StageLemma14113) (hU : CountSideU) (hD : CountStrongD)
    (hT : CountTHat) (hC : CountCentralizer) : Input15325Count :=
  have hUt : CountSideUt := countSideUt_of_strong countIneq_of_abstract hU hD
  input15325Count_of_narrow countExists_of_ctx hU hUt countIneq_of_abstract hT
    (countFinal_of_narrow h113 hC
      (countJS0_of_narrow hC (countS0Max_of_inputs countExists_of_ctx hU hUt hC)))

end CFSG.Quasithin
