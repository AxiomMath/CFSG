module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsSixInputs
import Certificates.Kernel.LocalQT.Small.C4051
import Certificates.Kernel.LocalQT.Small.C4051Rank

public section

namespace Certificates

open CFSG.KD.LQT.C4051 CFSG.QuasithinUnique.Unc25K1.Six in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25K1 CFSG.QuasithinUnique.Unc25K1.Six in
open Equiv in
theorem certificate4051 : (d0L.length = 8 ∧ saL.length = 24 ∧ sbL.length = 24 ∧ d0L.Nodup ∧ saL.Nodup ∧
          sbL.Nodup)
    ∧ (closedB (d0Gens.map R6.enc) d0L = true ∧
          closedB (saGens.map R6.enc) saL = true ∧ closedB (sbGens.map R6.enc) sbL = true)
    ∧ (∀ x : CFSG.QuasithinUnique.Unc25K1.Six.P6, Perm.sign x = 1 → R6.enc x ∈ saL ∨ R6.enc x ∈ sbL ∨
          ∃ r ∈ repsP, ∃ d ∈ d0L, ∃ e ∈ d0L, R6.enc x = d * R6.enc r * e)
    ∧ (∀ x : CFSG.QuasithinUnique.Unc25K1.Six.P6, Perm.sign x = 1 → ∀ L ∈ repLs, R6.enc x ∈ L)
    ∧ (∀ τ : CFSG.QuasithinUnique.Unc25K1.Six.P6, (d0Gens.map R6.enc).all (conjIn (R6.enc τ) d0L) = true →
          (saGens.map R6.enc).all (conjIn (R6.enc τ) saL) = true ∧
          (sbGens.map R6.enc).all (conjIn (R6.enc τ) sbL) = true) :=
  CFSG.KC.LQT.X6.s4051k hrank d0Gens saGens sbGens repsP h0 ha hb hr hk

end Certificates
