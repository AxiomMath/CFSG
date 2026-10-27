module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsTauInputs
import Certificates.Kernel.LocalQT.Small.C4041

public section

namespace Certificates

open CFSG.KD.LQT.C4041 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25K1 in
theorem certificate4041 : (∀ r ∈ rawList, rmul r (rr x1S) ≠ rmul (rcof (rr x1S)) r)
    ∧ (∀ r ∈ rawList, rmul r (rcof r) = rone →
          ∃ h ∈ rawList, rmul r (rcof h) = h)
    ∧ (∀ r ∈ rawList, (∀ t ∈ TlS.map rr, rmul r (rcof t) = rmul t r) →
          rmul r (rcof r) = rr u0S)
    ∧ (∀ a ∈ invR, ∀ b ∈ invR, ∀ c ∈ invR, rmul a b = rmul b a → rmul a c = rmul c a →
          rmul b c = rmul c b → a ≠ b → c ≠ a → c ≠ b → c ≠ rmul a b → False)
    ∧ (∀ a ∈ invR, ∀ b ∈ invR, a ≠ b → rmul a b = rmul b a →
          ∃ g ∈ rawList, rmul g (rr u0S) = rmul a g ∧ rmul g (rr d2S) = rmul b g)
    ∧ (∀ r ∈ rawList, rmul r (rr u0S) = rmul (rr u0S) r →
          rmul r (rr d2S) = rmul (rr d2S) r →
          r = rone ∨ r = rr u0S ∨ r = rr d2S ∨ r = rmul (rr u0S) (rr d2S))
    ∧ (rmul (rr d2S) (rr d2S) = rone ∧
          rmul (rr u0S) (rr d2S) = rmul (rr d2S) (rr u0S) ∧ rr d2S ≠ rone ∧ rr u0S ≠ rr d2S ∧
          rcof (rr u0S) = rr u0S ∧ rcof (rr d2S) = rr d2S) :=
  CFSG.KC.LQT.R.s4041k _ CFSG.KC.LQT.R.mem_rawList _ _ _ _ hx hu hd ht hk hs

end Certificates
