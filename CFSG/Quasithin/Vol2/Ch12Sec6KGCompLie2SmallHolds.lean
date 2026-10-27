module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2FourL34
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2FourU34
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2FourSp44
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2FourSL34
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2FourG24
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompD4Small

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem comp12626Lie2Four_holds :
    Comp12626Lie2Four := by
  intro Q _ K L P T v hQ h hK
  rcases hK with hK | hK | hK | hK | hK | ⟨s, hs⟩
  · exact not_psl34 hQ h hK
  · exact not_psu34 hQ h hK
  · exact not_psp44 hQ h hK
  · exact not_g24 hQ h hK
  · exact not_3d44 hQ h hK
  · cases s
    · exact not_su34 hQ h hs
    · exact not_sl34 hQ h hs

theorem comp12626Lie2Two_holds :
    Comp12626Lie2Two :=
  comp12626Lie2Two_of_d42 comp12626D42_holds

end CFSG.Quasithin.H13.S126C
