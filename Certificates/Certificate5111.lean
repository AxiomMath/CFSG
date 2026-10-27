module

public import CFSG.GH74.KGroups.CoverJ3Inputs
import Certificates.Kernel.CovJ3.Check
import CFSG.Certificates.Kernel.CovJ3Sound
import CFSG.Certificates.Kernel.OpsKSound
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

open CFSG.KC.OpsK CFSG.KC.OpsV4 CFSG.KC.CovJ3 CFSG.SectionRank.Native CFSG.GH74.KGroups.J3
  CertificateChecks.KernelJ3L

namespace Certificates

open CertificateChecks

set_option compiler.extract_closed false in
open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.J3 in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate5111 : conjCheck (ops2 80) (include_str "../CFSG/Blueprint/Data/J3G1-f2r80B0.m1")
      (include_str "../CFSG/Blueprint/Data/J3G1-f2r80B0.m2") j3Words (List.range 80) = true := by
  have jA : (ops2 80).decode CFSG.Blueprint.NativeSporadic.J3Seed1 =
      (hom2 80 (by norm_num)).U JA.M := by
    rw [JA.eq]
    exact CFSG.KC.Co1F2.bind_sound JA.bind
  have jB : (ops2 80).decode CFSG.Blueprint.NativeSporadic.J3Seed2 =
      (hom2 80 (by norm_num)).U JB.M := by
    rw [JB.eq]
    exact CFSG.KC.Co1F2.bind_sound JB.bind
  have hK := KernelCovJ3.ch5111_K
  rw [conjT_eq] at hK
  exact conjCheckAux_of_sim (Sim.ofHom (hom2 80 (by norm_num))) ⟨jA, trivial⟩ ⟨jB, trivial⟩
    (fun _ _ => trivial) hK

end Certificates
