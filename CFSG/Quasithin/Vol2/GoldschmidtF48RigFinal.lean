module

public import CFSG.Quasithin.Vol2.GoldschmidtF48RigConc
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigL3Main
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigSpMain

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin.H13.F48Rig

theorem f431F48_psl (f : ℕ) (hf : 2 ≤ f) (hm : F431ModelFacts .PSL 3 f) : F431F48 .PSL 3 f hm :=
  f431F48_of_model hm (f431Facts45_psl f hm) (f431Generation_psl3 f)
    (fun D _ hD A => cartanFPF_psl3 f hf hm D hD A)
    (fun D _ hD A => faithfulOnType_psl3 f hm D hD A _)

theorem f431F48_psp (f : ℕ) (hf : 2 ≤ f) (hm : F431ModelFacts .PSp 2 f) : F431F48 .PSp 2 f hm :=
  f431F48_of_model hm (f431Facts45_psp f hm) (f431Generation_psp f)
    (fun D _ hD A => cartanFPF_psp f hf hm D hD A)
    (fun D _ hD A => faithfulOnType_psp f hm D hD A _)

end CFSG.Quasithin.H13.F431
