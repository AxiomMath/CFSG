module

public import Certificates.Data.HePresData
public meta import Certificates.Kernel.SporSch.HN.GenHNX
public import Certificates.Kernel.SporSch.HN.GenHNX

public section

set_option maxRecDepth 200000

open CFSG.ComponentClassification.AS81.HePres.Native

#kss_strlits CertificateChecks.KernelCosetJ.HeImgStr.w0 hePiHeWord0
#kss_strlits CertificateChecks.KernelCosetJ.HeImgStr.w1 hePiHeWord1
#kss_strlits CertificateChecks.KernelCosetJ.HeImgStr.w2 hePiHeWord2
#kss_strlits CertificateChecks.KernelCosetJ.HeImgStr.w3 hePiHeWord3
#kss_strlits CertificateChecks.KernelCosetJ.HeImgStr.w4 hePiHeWord4
#kss_strlits CertificateChecks.KernelCosetJ.HeImgStr.w5 hePiHeWord5
#kss_strlits CertificateChecks.KernelCosetJ.HeImgStr.w6 hePiHeWord6
#kss_strlits CertificateChecks.KernelCosetJ.HeImgStr.w7 hePiHeWord7

namespace CertificateChecks.KernelCosetJ.HeImgStr

@[expose] noncomputable def W0 : List Char :=
  w0.c0 ++ w0.c1 ++ w0.c2 ++ w0.c3 ++ w0.c4 ++ w0.c5 ++ w0.c6 ++ w0.c7 ++ w0.c8 ++ w0.c9 ++ w0.c10
    ++ w0.c11 ++ w0.c12 ++ w0.c13 ++ w0.c14 ++ w0.c15 ++ w0.c16 ++ w0.c17 ++ w0.c18

theorem w0_toList : hePiHeWord0.toList = W0 := by
  unfold hePiHeWord0
  simp only [String.toList_append, String.toList_ofList, w0.e0, w0.e1, w0.e2, w0.e3, w0.e4, w0.e5,
    w0.e6, w0.e7, w0.e8, w0.e9, w0.e10, w0.e11, w0.e12, w0.e13, w0.e14, w0.e15, w0.e16, w0.e17,
    w0.e18]
  rfl

@[expose] noncomputable def W1 : List Char :=
  w1.c0 ++ w1.c1 ++ w1.c2 ++ w1.c3 ++ w1.c4 ++ w1.c5 ++ w1.c6 ++ w1.c7 ++ w1.c8 ++ w1.c9 ++ w1.c10
    ++ w1.c11 ++ w1.c12 ++ w1.c13 ++ w1.c14 ++ w1.c15 ++ w1.c16 ++ w1.c17 ++ w1.c18 ++ w1.c19 ++
    w1.c20 ++ w1.c21 ++ w1.c22 ++ w1.c23 ++ w1.c24 ++ w1.c25 ++ w1.c26 ++ w1.c27 ++ w1.c28 ++
    w1.c29 ++ w1.c30

theorem w1_toList : hePiHeWord1.toList = W1 := by
  unfold hePiHeWord1
  simp only [String.toList_append, String.toList_ofList, w1.e0, w1.e1, w1.e2, w1.e3, w1.e4, w1.e5,
    w1.e6, w1.e7, w1.e8, w1.e9, w1.e10, w1.e11, w1.e12, w1.e13, w1.e14, w1.e15, w1.e16, w1.e17,
    w1.e18, w1.e19, w1.e20, w1.e21, w1.e22, w1.e23, w1.e24, w1.e25, w1.e26, w1.e27, w1.e28,
    w1.e29, w1.e30]
  rfl

@[expose] noncomputable def W2 : List Char :=
  w2.c0 ++ w2.c1 ++ w2.c2 ++ w2.c3 ++ w2.c4 ++ w2.c5 ++ w2.c6 ++ w2.c7 ++ w2.c8 ++ w2.c9 ++ w2.c10
    ++ w2.c11 ++ w2.c12 ++ w2.c13 ++ w2.c14 ++ w2.c15 ++ w2.c16 ++ w2.c17 ++ w2.c18 ++ w2.c19 ++
    w2.c20 ++ w2.c21

theorem w2_toList : hePiHeWord2.toList = W2 := by
  unfold hePiHeWord2
  simp only [String.toList_append, String.toList_ofList, w2.e0, w2.e1, w2.e2, w2.e3, w2.e4, w2.e5,
    w2.e6, w2.e7, w2.e8, w2.e9, w2.e10, w2.e11, w2.e12, w2.e13, w2.e14, w2.e15, w2.e16, w2.e17,
    w2.e18, w2.e19, w2.e20, w2.e21]
  rfl

@[expose] noncomputable def W3 : List Char :=
  w3.c0 ++ w3.c1 ++ w3.c2 ++ w3.c3 ++ w3.c4 ++ w3.c5 ++ w3.c6 ++ w3.c7 ++ w3.c8 ++ w3.c9 ++ w3.c10
    ++ w3.c11 ++ w3.c12 ++ w3.c13 ++ w3.c14 ++ w3.c15 ++ w3.c16 ++ w3.c17 ++ w3.c18 ++ w3.c19 ++
    w3.c20 ++ w3.c21 ++ w3.c22 ++ w3.c23 ++ w3.c24 ++ w3.c25 ++ w3.c26

theorem w3_toList : hePiHeWord3.toList = W3 := by
  unfold hePiHeWord3
  simp only [String.toList_append, String.toList_ofList, w3.e0, w3.e1, w3.e2, w3.e3, w3.e4, w3.e5,
    w3.e6, w3.e7, w3.e8, w3.e9, w3.e10, w3.e11, w3.e12, w3.e13, w3.e14, w3.e15, w3.e16, w3.e17,
    w3.e18, w3.e19, w3.e20, w3.e21, w3.e22, w3.e23, w3.e24, w3.e25, w3.e26]
  rfl

@[expose] noncomputable def W4 : List Char :=
  w4.c0 ++ w4.c1 ++ w4.c2 ++ w4.c3 ++ w4.c4 ++ w4.c5 ++ w4.c6 ++ w4.c7 ++ w4.c8 ++ w4.c9 ++ w4.c10
    ++ w4.c11 ++ w4.c12 ++ w4.c13 ++ w4.c14 ++ w4.c15 ++ w4.c16 ++ w4.c17 ++ w4.c18 ++ w4.c19 ++
    w4.c20 ++ w4.c21 ++ w4.c22 ++ w4.c23 ++ w4.c24 ++ w4.c25 ++ w4.c26 ++ w4.c27 ++ w4.c28 ++
    w4.c29

theorem w4_toList : hePiHeWord4.toList = W4 := by
  unfold hePiHeWord4
  simp only [String.toList_append, String.toList_ofList, w4.e0, w4.e1, w4.e2, w4.e3, w4.e4, w4.e5,
    w4.e6, w4.e7, w4.e8, w4.e9, w4.e10, w4.e11, w4.e12, w4.e13, w4.e14, w4.e15, w4.e16, w4.e17,
    w4.e18, w4.e19, w4.e20, w4.e21, w4.e22, w4.e23, w4.e24, w4.e25, w4.e26, w4.e27, w4.e28,
    w4.e29]
  rfl

@[expose] noncomputable def W5 : List Char :=
  w5.c0 ++ w5.c1 ++ w5.c2 ++ w5.c3 ++ w5.c4 ++ w5.c5 ++ w5.c6 ++ w5.c7 ++ w5.c8 ++ w5.c9 ++ w5.c10
    ++ w5.c11 ++ w5.c12 ++ w5.c13 ++ w5.c14 ++ w5.c15 ++ w5.c16 ++ w5.c17 ++ w5.c18

theorem w5_toList : hePiHeWord5.toList = W5 := by
  unfold hePiHeWord5
  simp only [String.toList_append, String.toList_ofList, w5.e0, w5.e1, w5.e2, w5.e3, w5.e4, w5.e5,
    w5.e6, w5.e7, w5.e8, w5.e9, w5.e10, w5.e11, w5.e12, w5.e13, w5.e14, w5.e15, w5.e16, w5.e17,
    w5.e18]
  rfl

@[expose] noncomputable def W6 : List Char :=
  w6.c0 ++ w6.c1 ++ w6.c2

theorem w6_toList : hePiHeWord6.toList = W6 := by
  unfold hePiHeWord6
  simp only [String.toList_append, String.toList_ofList, w6.e0, w6.e1, w6.e2]
  rfl

@[expose] noncomputable def W7 : List Char :=
  w7.c0 ++ w7.c1 ++ w7.c2

theorem w7_toList : hePiHeWord7.toList = W7 := by
  unfold hePiHeWord7
  simp only [String.toList_append, String.toList_ofList, w7.e0, w7.e1, w7.e2]
  rfl

end CertificateChecks.KernelCosetJ.HeImgStr

end
