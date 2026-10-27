module

public import CFSG.RankThree.Co2.JUniqueCert
public import CFSG.RankThree.Co2.JUniqueM
public import Certificates.Certificate8106
public import Certificates.Certificate8108
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate16022
public import Certificates.Certificate3025
public import Certificates.Certificate3054
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3138

public noncomputable section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem jFacts_cert : JFacts where
  sq := Certificates.certificate8106.1
  comm := Certificates.certificate8106.2.1
  bij := Certificates.certificate8106.2.2.1
  le := Certificates.certificate8106.2.2.2.1
  norm := Certificates.certificate8106.2.2.2.2.1
  cent _ := Certificates.certificate8106.2.2.2.2.2.1
  ea _ := Certificates.certificate8106.2.2.2.2.2.2


theorem card_J : Nat.card (subW jWords) = 1024 := JM.card_J jFacts_cert

instance : Finite (subW jWords) := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)

theorem elemTwo_J : ElemTwo (subW jWords) := JM.elemTwo_J jFacts_cert

theorem eq_J_of_elemTwo {A : Subgroup Cr}
    (hAT : A ≤ subW sylWords) (hA : ElemTwo A) (hcard : Nat.card A = 1024) : A = subW jWords :=
  JM.eq_J_of_elemTwo jFacts_cert hAT hA hcard

theorem exists_conj_J_of_elemTwo {A : Subgroup Cr}
    (hA : ElemTwo A) (hcard : Nat.card A = 1024) :
    ∃ g : Cr, A = (subW jWords).map (MulAut.conj g).toMonoidHom :=
  JM.exists_conj_J_of_elemTwo jFacts_cert hA hcard

end CFSG.RankThree.Co2
