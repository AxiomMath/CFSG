module

public import Certificates.Data.Kernel.LocalQT.Tab2

public section

namespace CFSG.KC.J4Q

open CFSG.KC.LQT.T2

@[expose] noncomputable def mergeRunsK (rs : List (List Nat)) : List Nat :=
  List.flatten (Nat.rec (motive := fun _ => List (List Nat)) rs (fun _ ih => passK ih) 17)

end CFSG.KC.J4Q

end
