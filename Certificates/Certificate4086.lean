module

public import Certificates.Kernel.LocalQT.M23D.Cyc
public import Certificates.Kernel.LocalQT.M23D.Orb

public section

namespace Certificates

open CFSG.KD.LQT.M23D

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.Covers in
open CFSG.Sporadic.Schreier CFSG.Blueprint TauCeti in
open scoped Pointwise in
theorem certificate4086 : (wordVal yM m11R1 = 1)
    ∧ (wordVal yM m11R2 = 1)
    ∧ (yM 0 ≠ 1)
    ∧ (alphaG • D23 = D23)
    ∧ (betaG • D23 = D23)
    ∧ (orbitCheck = true)
    ∧ ((List.finRange 7).all (fun k => allEven (cycKeys k)) = true) :=
  ⟨yM_rel1, yM_rel2, yM_ne_one, alphaG_fix, betaG_fix, orbitCheck_eq, cycKeys_even⟩

end Certificates
