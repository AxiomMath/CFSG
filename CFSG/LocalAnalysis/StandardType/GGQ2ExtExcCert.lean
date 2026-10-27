module

public import Certificates.Certificate712526
public import Certificates.Certificate712527
public import Certificates.Certificate712528
public import Certificates.Certificate712529
public import Certificates.Certificate712530
public import Certificates.Certificate712531
public import Certificates.Certificate712532
public import Certificates.Certificate712533
public import Certificates.Certificate712534
public import Certificates.Certificate712535
public import Certificates.Certificate712536
public import Certificates.Certificate712537
public import Certificates.Certificate712538
public import Certificates.Certificate712539
public import Certificates.Certificate712540
public import Certificates.Certificate712541

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

theorem extCases_excRaw
    (m : Fin 6) : ExtCases (excRaw m) := by
  rw [extCases_iff_forall]
  intro vx
  have hc := code_lt m vx
  fin_cases m
  · exact Certificates.certificate712526 vx (Nat.zero_le _) (lt_of_lt_of_eq hc (by decide))
  · exact Certificates.certificate712527 vx (Nat.zero_le _) (lt_of_lt_of_eq hc (by decide))
  · exact Certificates.certificate712528 vx (Nat.zero_le _) (lt_of_lt_of_eq hc (by decide))
  · exact Certificates.certificate712529 vx (Nat.zero_le _) (lt_of_lt_of_eq hc (by decide))
  · have hc' : code 4 vx < 2187 := lt_of_lt_of_eq hc (by decide)
    by_cases h1 : code 4 vx < 547
    · exact Certificates.certificate712530 vx (Nat.zero_le _) h1
    by_cases h2 : code 4 vx < 1094
    · exact Certificates.certificate712531 vx (by omega) h2
    by_cases h3 : code 4 vx < 1641
    · exact Certificates.certificate712532 vx (by omega) h3
    exact Certificates.certificate712533 vx (by omega) (by omega)
  · have hc' : code 5 vx < 6561 := lt_of_lt_of_eq hc (by decide)
    by_cases h1 : code 5 vx < 821
    · exact Certificates.certificate712534 vx (Nat.zero_le _) h1
    by_cases h2 : code 5 vx < 1642
    · exact Certificates.certificate712535 vx (by omega) h2
    by_cases h3 : code 5 vx < 2463
    · exact Certificates.certificate712536 vx (by omega) h3
    by_cases h4 : code 5 vx < 3284
    · exact Certificates.certificate712537 vx (by omega) h4
    by_cases h5 : code 5 vx < 4105
    · exact Certificates.certificate712538 vx (by omega) h5
    by_cases h6 : code 5 vx < 4926
    · exact Certificates.certificate712539 vx (by omega) h6
    by_cases h7 : code 5 vx < 5747
    · exact Certificates.certificate712540 vx (by omega) h7
    exact Certificates.certificate712541 vx (by omega) (by omega)

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
