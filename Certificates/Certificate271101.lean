module

public import Certificates.Data.Inputs2711eJ3
import Certificates.Kernel.Gen2711.J3T
import CFSG.Certificates.Kernel.OpsMcertTXSound
import CFSG.Certificates.Kernel.OpsKSound
import CFSG.Certificates.Kernel.OpsF2FrGen

public section

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.KC.OpsMT CFSG.KC.OpsF2K
  CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.RankThree.Asc83Table.J3
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e CertificateChecks.KernelJ3L

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e in
theorem certificate271101 : j3GenCheck = true := by
  have h80 : 0 < 80 := by norm_num
  have jA : (ops2 80).decode CFSG.Blueprint.NativeSporadic.J3Seed1 = (hom2 80 h80).U JA.M := by
    rw [JA.eq]
    exact CFSG.KC.Co1F2.bind_sound JA.bind
  have jB : (ops2 80).decode CFSG.Blueprint.NativeSporadic.J3Seed2 = (hom2 80 h80).U JB.M := by
    rw [JB.eq]
    exact CFSG.KC.Co1F2.bind_sound JB.bind
  have hrA : 0 < j3GenData.nregs := by decide
  have hrB : 1 < j3GenData.nregs := by decide
  obtain ⟨hm, h0, h1, hx⟩ := seedsXT_sound (opsF2K 80) (hom2 80 h80) jA jB trivial trivial hrA hrB
    KernelGen2711J3.gen271101T_K
  unfold j3GenCheck
  rw [genCheck_fr_eq, genCheck_of hm h0 h1 KernelGen2711J3.gen271101T_D, Bool.true_and]
  unfold j3GenCross
  dsimp only
  obtain ⟨e1, -⟩ := regsOf_fr_eq (d := 80) CFSG.Blueprint.NativeSporadic.J3Seed1
    CFSG.Blueprint.NativeSporadic.J3Seed2 j3GenData.nregs j3GenData.prog
  obtain ⟨e2, s2⟩ := regsOf_fr_eq (d := 80) CFSG.Blueprint.NativeSporadic.J3Seed1
    CFSG.Blueprint.NativeSporadic.J3Seed2 j3Cert.nregs j3Cert.prog
  rw [e1, e2, evalW_fr_eq s2, evalW_fr_eq s2, eq_fr, eq_fr,
    hx (4, basisW j3Cert.rb 9) List.mem_cons_self,
    hx (5, basisW j3Cert.rb 10) (List.mem_cons_of_mem _ List.mem_cons_self)]
  rfl

end Certificates
