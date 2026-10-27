module

public import CFSG.Quasithin.H13.GoldschmidtU43CRel

public section

namespace CFSG.Quasithin.H13.U43

variable {K L : Type} [Group K] [Group L] (f : K →* L)

theorem JW13.map {a s u v : K} (h : JW13 a s u v) : JW13 (f a) (f s) (f u) (f v) where
  r1 := by simpa [map_pow] using congrArg f h.r1
  r2 := by simpa [map_mul, map_inv, map_pow] using congrArg f h.r2
  r3 := by simpa [map_mul, map_inv] using congrArg f h.r3
  r4 := by simpa [map_mul, map_inv] using congrArg f h.r4
  r5 := by simpa [map_mul, map_inv, map_pow] using congrArg f h.r5
  r6 := by simpa [map_mul, map_inv] using congrArg f h.r6
  r7 := by simpa [map_mul, map_inv] using congrArg f h.r7
  r8 := by simpa [map_mul, map_inv] using congrArg f h.r8
  r9 := by simpa [map_mul, map_inv] using congrArg f h.r9
  r10 := by simpa [map_mul, map_inv] using congrArg f h.r10
  r11 := by simpa [map_mul, map_inv, map_pow] using congrArg f h.r11
  r12 := by simpa [map_pow] using congrArg f h.r12
  r13 := by simpa [map_mul, map_inv] using congrArg f h.r13

end CFSG.Quasithin.H13.U43
