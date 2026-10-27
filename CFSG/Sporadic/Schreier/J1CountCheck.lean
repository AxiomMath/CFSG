module

public import CFSG.Sporadic.Schreier.J1Tables
public import CFSG.Sporadic.Schreier.ClassSum
public meta import CFSG.Sporadic.Schreier.J1Tables
public meta import CFSG.Sporadic.Schreier.ClassSum
public import CFSG.Sporadic.Schreier.J1CountCheckInputs
public import Certificates.Certificate2166

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem j1_gen_checks :
    invOK 3080 j1ATbl j1AInvTbl = true ∧ invOK 3080 j1BTbl j1BInvTbl = true ∧
      ordTest 3080 2 j1ATbl = true ∧ ordTest 3080 3 j1BTbl = true ∧
      pairTest 3080 7 19 2 3 j1ATbl j1BTbl = true :=
  Certificates.certificate2166.1

theorem j1_count_two : (j1OrderTables 2).length = 1463 :=
  Certificates.certificate2166.2.1

theorem j1_count_three : (j1OrderTables 3).length = 5852 :=
  Certificates.certificate2166.2.2.1

theorem j1_classOK : classOK 3080 j1GenTbls j1GenInvTbls (j1OrderTables 2) 2000 = true :=
  Certificates.certificate2166.2.2.2.1

theorem j1_classTotal :
    classTotal 3080 j1GenTbls j1GenInvTbls (j1OrderTables 2) (j1OrderTables 3) 2000 7 19 2 3 =
      175560 :=
  Certificates.certificate2166.2.2.2.2

end CFSG.Sporadic.Schreier
