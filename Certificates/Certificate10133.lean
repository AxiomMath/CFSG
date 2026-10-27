module

public import Certificates.Data.Fi22ThreeFix
import Certificates.Kernel.Fi22Reps.Final
import Certificates.Kernel.Fi22Reps.FixCount

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi22.S0
  CFSG.HardMathSupport.Foote.E27.Fi22S0 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three

theorem certificate10133 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native.fi22RepFixOK
    (CFSG.Sporadic.Fi22.Native.orbitData ()) = true := by
  have key : ∀ k < 4, fixCount22 (eltT par (genT CFSG.Sporadic.Fi22.orb) globRep[k]!) =
      CFSG.KC.Fi22Reps.fixCntK (KernelFi22Reps.xT k) := by
    intro k hk
    have hT := rep_eltT _ (globRep_lt k hk)
    have hX := CFSG.KD.Fi22Reps.repE_iff.1 (KernelFi22Reps.rep_xT hk)
    unfold fixCount22 CFSG.KC.Fi22Reps.fixCntK
    refine congrArg List.length (List.filter_congr fun i hi => ?_)
    have hi' := List.mem_range.1 hi
    rw [hT i hi', hX i hi', xRep_def]
  obtain ⟨h0, h1, h2, h3⟩ := KernelFi22Reps.ch10133fix
  change fi22RepFixOK CFSG.Sporadic.Fi22.orb = true
  unfold fi22RepFixOK
  dsimp only
  rw [key 0 (by norm_num), key 1 (by norm_num), key 2 (by norm_num), key 3 (by norm_num),
    h0, h1, h2, h3]
  rfl

end Certificates
