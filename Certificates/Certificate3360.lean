
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneSylowGroup
import Certificates.Kernel.Misc.Oq.Facts
import Certificates.Kernel.Misc.Oq.Group
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataKill
import Certificates.Kernel.Misc.Oq.Reps

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.Misc.Oq CertificateChecks.KernelMisc.Oq

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne in
theorem certificate3360 : ∀ u : Bool,
    Nat.card (Gq u) = (if u then 362880 else 56448) ∧
    (∀ σ ∈ Gq u, sgnOK u (tupleOf σ) = true) ∧
    (∀ σ ∈ Gq u, u = true → bOf u (tupleOf σ) = idE →
      tupleOf σ = CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne.idT ∨ tupleOf σ = omT ∨ tupleOf σ = CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne.compT omT omT) ∧
    (∀ σ ∈ Gq u, isInvT (tupleOf σ) = true → presT u (tupleOf σ) = true →
      ∃ w, (∀ a ∈ w, a < 3) ∧ ∃ k, k < (killReps u).length ∧
        CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne.compT (evalW (tupleOf σ) w) (tupleOf σ) =
          CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne.compT ((killReps u).getD k ([], [])).1 (evalW (tupleOf σ) w)) ∧
    (∀ k, k < (killReps u).length → validT u ((killReps u).getD k ([], [])).1 = true ∧
      ∃ c, validCert u ((killReps u).getD k ([], [])).1 c = true) :=
  fun u => by
    cases u
    exacts [facts_of_checks (facts_of false 8 9 49 1152 72 partsL rfl stabL_parts rfl rfl rfl
        blocksL repL krPL_eq krPL_len),
      facts_of_checks (facts_of true 4 30 63 5760 120 partsU rfl stabU_parts rfl rfl rfl blocksU
        repU krPU_eq krPU_len)]

end Certificates

end
