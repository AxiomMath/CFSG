module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1OrdData
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public meta import Certificates.Data.CFSGNative.SectionRank.F2
import Certificates.Kernel.GLQ.Co1Ord
import Certificates.Kernel.TcGen.F2Glue
public import CFSG.Certificates.Kernel.OpsKSound
public import CFSG.Certificates.Kernel.OpsHom
import CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

open CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.Blueprint
open CFSG.EvenSporadicStandard.Induction.Co1Ord CertificateChecks.KernelTc
  CertificateChecks.KernelGLQ.Co1OrdK

namespace Certificates

noncomputable abbrev H27217 : Hom (ops2 24) (opsF2K 24) := hom2 24 (by norm_num)

open CFSG.EvenSporadicStandard.Induction.Co1Ord in
theorem certificate27217 : co1OrdCheck () = true := by
  have hk := kOrd
  unfold checkOrd at hk
  rw [forceB_eq, powN_eq _ _ _ _ (by norm_num), runK_eq, powN_eq _ _ _ _ (by norm_num),
    powN_eq _ _ _ _ (by norm_num)] at hk
  have hlt : co1OrdProg.all (Instr.lt 11) = true := by decide +kernel
  have eA : (ops2 24).decode NativeSporadic.Co1Seed1 = H27217.U C1A.M := c1A
  have eB : (ops2 24).decode NativeSporadic.Co1Seed2 = H27217.U C1B.M := c1B
  have hinit : initRegsN (ops2 24) 11 ((ops2 24).decode NativeSporadic.Co1Seed1,
      (ops2 24).decode NativeSporadic.Co1Seed1)
      ((ops2 24).decode NativeSporadic.Co1Seed2,
        (ops2 24).pow ((ops2 24).decode NativeSporadic.Co1Seed2) 2) =
      (initRegsN (opsF2K 24) 11 (C1A.M, C1A.M) (C1B.M, (opsF2K 24).pow C1B.M 2)).map
        H27217.UU := by
    rw [eA, eB, (H27217.pow_U 2 trivial).1]
    exact H27217.initRegsN_U 11 (C1A.M, C1A.M) (C1B.M, (opsF2K 24).pow C1B.M 2)
  obtain ⟨hrun, hsize, -⟩ := H27217.runProgN_U 11 co1OrdProg hlt
    (initRegsN (opsF2K 24) 11 (C1A.M, C1A.M) (C1B.M, (opsF2K 24).pow C1B.M 2))
    (by unfold initRegsN; exact Array.size_ofFn)
    (H27217.initRegsN_P ⟨trivial, trivial⟩ ⟨trivial, trivial⟩)
  unfold co1OrdCheck co1OrdRegs
  rw [hlt, Bool.true_and, hinit, hrun, get_map _ H27217.UU (by rw [hsize]; decide)]
  simp only [Hom.UU]
  rw [(H27217.pow_U 16 trivial).1, (H27217.pow_U 8 trivial).1, H27217.one.1,
    H27217.eq trivial trivial, (H27217.unit 0).1, (H27217.vmul trivial trivial).1,
    H27217.vne trivial trivial]
  exact hk

end Certificates
