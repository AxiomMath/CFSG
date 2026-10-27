module

public import Certificates.Certificate712511
public import Certificates.Certificate712512
public import Certificates.Certificate712513
public import Certificates.Certificate712514
public import Certificates.Certificate712515
public import Certificates.Certificate712516
public import Certificates.Certificate712517
public import Certificates.Certificate712518
public import Certificates.Certificate712519
public import Certificates.Certificate712520
public import Certificates.Certificate712521
public import Certificates.Certificate712522
public import Certificates.Certificate712523
public import Certificates.Certificate712524

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

theorem censusCasesVx_five
    (vx : V 5) : CensusCasesVx (excRaw 5) vx := by
  have hd : 3 ^ dim 5 = 6561 := by decide
  have hc := code_lt 5 vx
  rw [hd] at hc
  by_cases h1 : code 5 vx < 821
  · exact Certificates.certificate712517 vx (by omega) (by omega)
  by_cases h2 : code 5 vx < 1642
  · exact Certificates.certificate712518 vx (by omega) (by omega)
  by_cases h3 : code 5 vx < 2463
  · exact Certificates.certificate712519 vx (by omega) (by omega)
  by_cases h4 : code 5 vx < 3284
  · exact Certificates.certificate712520 vx (by omega) (by omega)
  by_cases h5 : code 5 vx < 4105
  · exact Certificates.certificate712521 vx (by omega) (by omega)
  by_cases h6 : code 5 vx < 4926
  · exact Certificates.certificate712522 vx (by omega) (by omega)
  by_cases h7 : code 5 vx < 5747
  · exact Certificates.certificate712523 vx (by omega) (by omega)
  exact Certificates.certificate712524 vx (by omega) (by omega)

theorem censusCases_excRaw
    (m : Fin 6) : CensusCases (excRaw m) := by
  rw [censusCases_iff_forall]
  fin_cases m
  · exact Certificates.certificate712511
  · exact Certificates.certificate712512
  · exact Certificates.certificate712513
  · exact Certificates.certificate712514
  · exact Certificates.certificate712515
  · exact censusCasesVx_five

theorem inLLeafOrSelCases_excRaw_four :
    InLLeafOrSelCases (excRaw 4) :=
  Certificates.certificate712516

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
