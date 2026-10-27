module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Words
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3Inputs
import Certificates.Kernel.LocalQT.Small.C4145

public section

namespace Certificates

open CFSG.KD.LQT.C4145 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25K1 in
open scoped MatrixGroups in
theorem certificate4145 : (u0S ≠ 1)
    ∧ (u0S ^ 2 = 1)
    ∧ (Fintype.card S3 = 5616)
    ∧ (∀ r ∈ rawList,
          (((rmul r (rr u0S) = rmul (rr u0S) r ∧ rmul r (rmul r r) = rone) ↔ r ∈ TlS.map rr) ∧
            (rmul r (rr u0S) = rmul (rr u0S) r → (∀ t ∈ TlS.map rr, rmul t r = rmul r t) →
              r = rone ∨ r = rr u0S) ∧
            ((∀ t ∈ TlS.map rr, rmul r t = rmul t r) → r = rone ∨ r = rr u0S)))
    ∧ (∀ u ∈ rawList, u ≠ rone → rmul u u = rone →
          ∃ g ∈ rawList, rmul g (rr u0S) = rmul u g)
    ∧ (∀ t ∈ TlS, ∃ w ∈ WsS, t = evB aS bS w)
    ∧ (u0S = evB aS bS [true, false, true, false])
    ∧ (aS ≠ 1 ∧ bS ≠ 1 ∧ (aS * bS) ^ 2 ≠ 1 ∧ (aS * bS) ^ 4 = 1)
    ∧ (PlS.length ≤ 24) :=
  CFSG.KC.LQT.R.s4145k _ CFSG.KC.LQT.R.mem_rawList _ _ _ _ _ hu ha hb ht hk hs

end Certificates
