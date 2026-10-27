module

import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Data.Kernel.B3SixEval
public import CFSG.Quasithin.Background.B3FourData
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B1Solvable
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.B3VMod

#kc_eval CFSG.KC.B3Six dG0 CFSG.KC.B3Six.Ev.four 0 1
#kc_eval CFSG.KC.B3Six dGT0 CFSG.KC.B3Six.Ev.four 1 1
#kc_eval CFSG.KC.B3Six dL0 CFSG.KC.B3Six.Ev.four 0 0
#kc_eval CFSG.KC.B3Six dLT0 CFSG.KC.B3Six.Ev.four 1 0

public section

namespace CFSG.KC.B3Six

open CFSG.Quasithin.B3

@[expose] noncomputable def dG0D : FourD :=
  ⟨dG0.T, dG0.H1, dG0.H2, dG0.R1, dG0.R2, dG0.L1, dG0.L2T, dG0.L1d, dG0.A1p, dG0.w⟩

@[expose] noncomputable def dGT0D : FourD :=
  ⟨dGT0.T, dGT0.H1, dGT0.H2, dGT0.R1, dGT0.R2, dGT0.L1, dGT0.L2T, dGT0.L1d, dGT0.A1p, dGT0.w⟩

@[expose] noncomputable def dL0D : FourD :=
  ⟨dL0.T, dL0.H1, dL0.H2, dL0.R1, dL0.R2, dL0.L1, dL0.L2T, dL0.L1d, dL0.A1p, dL0.w⟩

@[expose] noncomputable def dLT0D : FourD :=
  ⟨dLT0.T, dLT0.H1, dLT0.H2, dLT0.R1, dLT0.R2, dLT0.L1, dLT0.L2T, dLT0.L1d, dLT0.A1p, dLT0.w⟩

end CFSG.KC.B3Six

end
