module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverCheck
import Certificates.Kernel.LocalQT.Cov.C4101
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.LocalQTCovSound
import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.Certificates.NativeSchreierCard
import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
import CFSG.Open.Defs

public section

namespace Certificates

open CFSG.KD.LQT.C4101 CFSG.KC.LQT.Cov CFSG.KC.LQT.W CFSG.Sporadic.Mathieu
  CFSG.QuasithinUnique.Ch1.M22Cover

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.M22Cover in
theorem certificate4101 : (covCheck covData = true)
    ∧ (covData.nV = 128)
    ∧ (covData.free = [189]) := by
  have hA : codeP m22gA = 228952723507329932679484465855724 := by decide +kernel
  have hB : codeP m22gB = 81506110577382089737470578414133 := by decide +kernel
  have h := cov_sound CT.chars H 128 [189] hA hB kC
  rw [← CT.eq] at h
  exact h

end Certificates
