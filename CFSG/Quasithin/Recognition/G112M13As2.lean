module

public import CFSG.Quasithin.Recognition.G112M13As8

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG

section G11_2


theorem as_G_11_2M
    : G_11_2M :=
  CFSG.ASVolI.ChG.g112Canonical_of_lemmasM g114Canonical_holdsM g115Canonical_holdsM
    g115ComponentCanonical_holdsM g116Canonical_holdsM as_G_11_8M as_G_11_9M
    g11CanonicalCentralizerOnI_holdsM
    (fun V _ _ _ B Γ v₁ W X X₀ L cs I hI x hx hxC =>
      (g119Canonical_fullM V B Γ v₁ W X X₀ L cs I hI).2.2.2 x hx hxC)

end G11_2

end CFSG.ASVolI
