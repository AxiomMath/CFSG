module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenG23Data
public import CFSG.LieType.Multipliers.G23Data
public import CFSG.Sporadic.He.FpSpec
public import Certificates.Data.CFSGNative.SectionRank.F3
import Certificates.Kernel.TcGen.F3Glue
import Certificates.Kernel.TcGen.G23Rows
import Certificates.Kernel.Misc.Coset.C12042
import CFSG.Certificates.Kernel.LaneRowsSound

public section

namespace CertificateChecks.Batch9436

open CFSG.AGLEmbedding.R3 CFSG.Sporadic.He.Native CFSG.LieType.Multipliers.G23 CFSG.Blueprint
  CFSG.KC.LocalComp.Ops3Snd CFSG.KC.LaneRows CFSG.KC.MiscCoset.Mat CertificateChecks.KernelTc
  CertificateChecks.KernelMiscCoset.C12042

theorem decode_a : NativeSporadic.decode 3 14 1 G23Three.seedA = toMat 3 14 aArr := by
  have h1 : NativeSporadic.decode 3 14 1 G23Three.seedA = mat3 G23.lay G23.A := by
    rw [(mat3_decode G23.lay G23.lay_ok rfl G23.decA).2, ← G23.LA_eq]
    rfl
  have h2 : matL 3 14 aL = toMat 3 14 aArr := ma.trans (toMat_rootProd aWord).symm
  exact h1.trans ((mat3_eq_matL rfl G23.rowsA_K).trans h2)

theorem decode_b : NativeSporadic.decode 3 14 1 G23Three.seedB = toMat 3 14 bArr := by
  have h1 : NativeSporadic.decode 3 14 1 G23Three.seedB = mat3 G23.lay G23.B := by
    rw [(mat3_decode G23.lay G23.lay_ok rfl G23.decB).2, ← G23.LB_eq]
    rfl
  have h2 : matL 3 14 bL = toMat 3 14 bArr := mb.trans (toMat_rootProd bWord).symm
  exact h1.trans ((mat3_eq_matL rfl G23.rowsB_K).trans h2)

end CertificateChecks.Batch9436

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.R3 CertificateChecks.KernelTc

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.Sporadic.He.Native
  CFSG.LieType.Multipliers.G23 CFSG.Blueprint in
theorem certificate9436 : (cpCheck (ops3 14) G23Three.seedA G23Three.seedB G23Three.nregs G23Three.cpProg
      G23Three.cpSpec = true) ∧ (G23Three.cpSpec.noFun = true) ∧
    (NativeSporadic.decode 3 14 1 G23Three.seedA = CFSG.Sporadic.He.Native.toMat 3 14 aArr) ∧
    (NativeSporadic.decode 3 14 1 G23Three.seedB = CFSG.Sporadic.He.Native.toMat 3 14 bArr) :=
  ⟨cp3_of G23.lay_ok rfl rfl G23.decA G23.decB G23.LA_eq G23.LB_eq (by decide +kernel) G23.cp_K,
    by decide +kernel, CertificateChecks.Batch9436.decode_a, CertificateChecks.Batch9436.decode_b⟩

end Certificates
