module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreONSevenData
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.TcGen.CoreON
import CFSG.Certificates.Kernel.OpsLayMcertSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace Certificates

open CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CFSG.Blueprint CertificateChecks.KernelTc

theorem coreGenCheck_eq_mcert {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String)
    (n : Nat) (prog : List Op) (D : RSpec) :
    coreGenCheck O sA sB n prog D = (mcertCheck O sA sB ⟨n, prog, D.facts⟩ &&
      decide (D.rA < n) && decide (D.rB < n) &&
      O.eq (O.regsOf sA sB n prog)[D.rA]! (O.decode sA) &&
      O.eq (O.regsOf sA sB n prog)[D.rB]! (O.decode sB) && D.wf) :=
  rfl

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint in
theorem certificate9514 : coreGenCheck (ops3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2
    CoreON7.nregs CoreON7.prog CoreON7.spec = true := by
  obtain ⟨hm, hrA, hrB, h0, h1⟩ :=
    seedsL_sound (d := 154) ON.lay_ok rfl rfl ON.decA ON.decB ON.LA_eq ON.LB_eq ON.core_K
  dsimp only at hrA hrB h0 h1
  have hw : CoreON7.spec.wf = true := by decide +kernel
  rw [coreGenCheck_eq_mcert, hm, decide_eq_true hrA, decide_eq_true hrB, h0, h1, hw]
  rfl

end Certificates
