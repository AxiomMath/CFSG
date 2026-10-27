module

public import CFSG.Sporadic.SmallOddCore.J3Data

public section

namespace Certificates.Odd87F3.J3

open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native

@[expose] def rowAt (i : Fin 2) : ClassRow :=
  j3Rows[i.val]'(by have h : j3Rows.length = 2 := by decide
                    omega)

end Certificates.Odd87F3.J3
