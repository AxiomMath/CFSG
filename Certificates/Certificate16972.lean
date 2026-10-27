module

public import CFSG.GF2Type.Smith1979.GammaU.FpfThreeInputs
import Certificates.Kernel.GammaU.FpfThreeOK
import CFSG.Certificates.Kernel.GammaUFpfThreeSound

public section

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.SigmaP CFSG.KC.GUK CFSG.KD.GUK

namespace Certificates

theorem kCheckAt_zero : kCheckAt 0 = true := by
  have hS : ∀ y, (s45 0).contains y = bitM SM0 y := fun y => by
    rw [← kf16972_sm0, bitM_maskL]
    rfl
  have hU : s45_0 = [12, 48, 51, 63, 204] ++ ([207, 240, 252, 255, 768] ++
      ([771, 780, 783, 819, 828] ++ ([831, 963, 972, 1008, 1011] ++
      ([1020, 3072, 3084, 3120, 3123] ++ ([3135, 3264, 3267, 3276, 3279] ++
      ([3315, 3324, 3327, 3843, 3855] ++ ([3888, 3891, 3903, 4032, 4035] ++
      [4044, 4047, 4083, 4092, 4095]))))))) := rfl
  have e1 : kBasis 0 = [12, 48, 51] := rfl
  have e2 : s45 0 = s45_0 := rfl
  have e3 : sigmaBasis 0 = [12, 48, 51, 204, 768, 3072] := rfl
  rw [kCheckAt, kf16972_cs0, kf16972_b0, kHead_eq, kTriples_eq hS, e1, e2, e3, kf16972_h0, congrArg (fun U => triplesK B60 s45_0 U SM0 CS0 [12, 48, 51]) hU]
  simp only [triplesK_append, kf16972_t0a, kf16972_t0b, kf16972_t0c, kf16972_t0d, kf16972_t0e,
    kf16972_t0f, kf16972_t0g, kf16972_t0h, kf16972_t0i, Bool.and_self]

theorem kCheckAt_one : kCheckAt 1 = true := by
  have hS : ∀ y, (s45 1).contains y = bitM SM1 y := fun y => by
    rw [← kf16972_sm1, bitM_maskL]
    rfl
  have hU : s45_1 = [5, 48, 136, 184, 320] ++ ([325, 373, 461, 509, 522] ++
      ([570, 575, 642, 647, 690] ++ ([695, 842, 890, 895, 1010] ++
      ([1015, 3072, 3077, 3120, 3208] ++ ([3213, 3256, 3261, 3440, 3528] ++
      ([3533, 3576, 3581, 3594, 3599] ++ ([3642, 3714, 3719, 3762, 3767] ++
      [3914, 3919, 3962, 4082, 4087]))))))) := rfl
  have e1 : kBasis 1 = [5, 48, 136] := rfl
  have e2 : s45 1 = s45_1 := rfl
  have e3 : sigmaBasis 1 = [5, 48, 136, 320, 522, 3072] := rfl
  rw [kCheckAt, kf16972_cs1, kf16972_b1, kHead_eq, kTriples_eq hS, e1, e2, e3, kf16972_h1, congrArg (fun U => triplesK B61 s45_1 U SM1 CS1 [5, 48, 136]) hU]
  simp only [triplesK_append, kf16972_t1a, kf16972_t1b, kf16972_t1c, kf16972_t1d, kf16972_t1e,
    kf16972_t1f, kf16972_t1g, kf16972_t1h, kf16972_t1i, Bool.and_self]

open CFSG.GF2Type.Smith1979.GammaU.SigmaP in
theorem certificate16972 : kCheck () = true :=
  by rw [kCheck, kCheckAt_zero, kCheckAt_one]; rfl

end Certificates
