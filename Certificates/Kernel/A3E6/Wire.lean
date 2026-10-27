module

public import Certificates.Kernel.A3E6.Roots
public import Certificates.Kernel.A3E6.TagsTw
public import Certificates.Kernel.A3E6.TagsUn
public import CFSG.Certificates.Kernel.A3E6.Sound
public import CFSG.Certificates.Kernel.A3E6.GlueAssembly

public section

namespace CertificateChecks.KernelA3E6

open Certificates.A3E6K CFSG.KC.A3E6 CFSG.StandardType.LieCore CFSG.StandardType.LieCore.A3E6K

@[expose] noncomputable def chunks : List (List (List (List (List ℕ)))) :=
  [fr0, fr1, fr2, fr3, fr4, fr5, fr6, fr7, fr8, fr9]

theorem chunks_length : chunks.length = 10 := rfl

theorem chunks_struct :
    ∀ c < chunks.length,
      framesStruct rootsP ZP NP FMP (chunks.getD c []) (27 * c) (27 * c + 27) = true := by
  intro c hc
  rw [chunks_length] at hc
  interval_cases c
  · exact ch715502s0
  · exact ch715502s1
  · exact ch715502s2
  · exact ch715502s3
  · exact ch715502s4
  · exact ch715502s5
  · exact ch715502s6
  · exact ch715502s7
  · exact ch715502s8
  · exact ch715502s9

theorem chunks_tw : ∀ c < chunks.length, framesTags true rootsP ZP (chunks.getD c []) = true := by
  intro c hc
  rw [chunks_length] at hc
  interval_cases c
  · exact ch715502t0
  · exact ch715502t1
  · exact ch715502t2
  · exact ch715502t3
  · exact ch715502t4
  · exact ch715502t5
  · exact ch715502t6
  · exact ch715502t7
  · exact ch715502t8
  · exact ch715502t9

theorem chunks_un : ∀ c < chunks.length, framesTags false rootsP ZP (chunks.getD c []) = true := by
  intro c hc
  rw [chunks_length] at hc
  interval_cases c
  · exact ch715502u0
  · exact ch715502u1
  · exact ch715502u2
  · exact ch715502u3
  · exact ch715502u4
  · exact ch715502u5
  · exact ch715502u6
  · exact ch715502u7
  · exact ch715502u8
  · exact ch715502u9


theorem masks_all : ∀ i < 72, masksAt rootsP ZP NP i = true := allN_sound ch715502m

theorem cover_all : ∀ i < 72, coverAt ZP NP FMP (cvRow cv0 cv1 i) i = true := allN_sound ch715502c

theorem a3SpecTwE6_kernel : A3SpecTwE6 :=
  a3SpecTwE6_of_frames (cover_sound ch715502rE masks_all cover_all chunks_length chunks_struct)
    (frames_sound ch715502rE masks_all chunks_struct)
    (tw_sound ch715502rE masks_all chunks_struct chunks_tw)

theorem a3SpecE6Struct_kernel : A3SpecE6Struct :=
  a3SpecE6Struct_of_frames (cover_sound ch715502rE masks_all cover_all chunks_length chunks_struct)
    (frames_sound ch715502rE masks_all chunks_struct)
    (un_sound ch715502rE masks_all chunks_struct chunks_un)

end CertificateChecks.KernelA3E6

end
