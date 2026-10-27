module

public import CFSG.Quasithin.Vol2.Ch9L34M64D

public section

namespace CFSG.Quasithin.H47W

open CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H.Mathieu

@[expose] def dat64four : List (List ℕ × List ℕ) :=
  dat64.map fun d => (d.1, pickWit 64 4 d.1)

@[expose] def chk64four : Bool :=
  dat64four.all fun d => AllLt 64 d.1 && rankOK 4 64 d.1 d.2

end CFSG.Quasithin.H47W
