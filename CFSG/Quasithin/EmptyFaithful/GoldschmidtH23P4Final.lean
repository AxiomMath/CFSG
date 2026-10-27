module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowLieB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowLieC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowLieE
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowLieF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporM11
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporM12
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporM22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporM23
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporM24
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporJ2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporHS
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporHe
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporRu
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4TitsC

public section

namespace CFSG.Quasithin.H23P4


theorem p4Rows_of_certs : P4Rows where
  alt6 := rowOK_alternating_six
  alt7 := rowOK_alternating_seven
  sl32 := rowOK_statedSL_three_two
  psl4 := rowOK_of_isPSL_four_two
  psl5 := rowOK_of_isPSL_five_two
  psu33 := rowOK_of_isPSU33
  d4 := rowOK_of_is3D4
  tits := rowTits_of_isTits
  m11 := rowOK_of_isSporadic_M11
  m12 := rowOK_of_isSporadic_M12
  m22 := rowOK_of_isSporadic_M22
  m23 := rowOK_of_isSporadic_M23
  m24 := rowOK_of_isSporadic_M24
  j2 := rowOK_of_isSporadic_J2
  hs := rowOK_of_isSporadic_HS
  he := rowOK_of_isSporadic_He
  ru := rowOK_of_isSporadic_Ru

theorem lemma15123FiveInputV_of_certs (h2c : Five2cTrivial) : Lemma15123FiveInputV :=
  lemma15123FiveInputV_of_rows p4Rows_of_certs h2c

end CFSG.Quasithin.H23P4
