module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieAsm
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieRed

public section

namespace CFSG.Quasithin.H13.F431.Un

theorem f431UnOutLieProp_four (f : ℕ) (hf : 2 ≤ f) : F431UnOutLieProp 4 f :=
  f431UnOutLieProp_of_model f hf fun _ _ _ h _ hY K₀ hinn hev =>
    exists_unOutRel h hf hY K₀ hinn hev

end CFSG.Quasithin.H13.F431.Un
