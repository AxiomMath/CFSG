module

public import CFSG.GH74.Uniqueness.SU.SU5F4
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointRels

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.GH74.Uniqueness.SU.SU5 (F4c)
open CFSG.GH74.Uniqueness.SU.SU5.F4c

@[expose] def nativeGen : Fin 18 → Matrix (Fin 6) (Fin 6) F4c := ![
  !![z0, z1, z0, z0, z0, z0; z1, z0, z0, z0, z0, z0; z0, z0, z1, z0, z0, z0; z0, z0, z0, z1, z0, z0; z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1],
  !![z0, w, z0, z0, z0, z0; w2, z0, z0, z0, z0, z0; z0, z0, z1, z0, z0, z0; z0, z0, z0, z1, z0, z0; z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z0, z1, z0, z0, z0; z0, z1, z0, z0, z0, z0; z0, z0, z0, z1, z0, z0; z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z0, w, z0, z0, z0; z0, w2, z0, z0, z0, z0; z0, z0, z0, z1, z0, z0; z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z1, z0, z0, z0, z0; z0, z0, z0, z1, z0, z0; z0, z0, z1, z0, z0, z0; z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z1, z0, z0, z0, z0; z0, z0, z0, w, z0, z0; z0, z0, w2, z0, z0, z0; z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z1, z0, z0, z0, z0; z0, z0, z1, z0, z0, z0; z0, z0, z0, z0, z1, z0; z0, z0, z0, z1, z0, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z1, z0, z0, z0, z0; z0, z0, z1, z0, z0, z0; z0, z0, z0, z0, w, z0; z0, z0, z0, w2, z0, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z1, z0, z0, z0, z0; z0, z0, z1, z0, z0, z0; z0, z0, z0, z1, z0, z0; z0, z0, z0, z0, z0, z1; z0, z0, z0, z0, z1, z0],
  !![z1, z0, z0, z0, z0, z0; z0, z1, z0, z0, z0, z0; z0, z0, z1, z0, z0, z0; z0, z0, z0, z1, z0, z0; z0, z0, z0, z0, z0, w; z0, z0, z0, z0, w2, z0],
  !![z1, w2, w2, z0, z0, z0; w, w2, w, z0, z0, z0; w, w, w2, z0, z0, z0; z0, z0, z0, z1, z0, z0; z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1],
  !![z1, w2, w, z0, z0, z0; z1, z1, z1, z0, z0, z0; z1, w, w2, z0, z0, z0; z0, z0, z0, z1, z0, z0; z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z1, w2, w2, z0, z0; z0, w, w2, w, z0, z0; z0, w, w, w2, z0, z0; z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z1, w2, w, z0, z0; z0, z1, z1, z1, z0, z0; z0, z1, w, w2, z0, z0; z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z1, z0, z0, z0, z0; z0, z0, z1, w2, w2, z0; z0, z0, w, w2, w, z0; z0, z0, w, w, w2, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z1, z0, z0, z0, z0; z0, z0, z1, w2, w, z0; z0, z0, z1, z1, z1, z0; z0, z0, z1, w, w2, z0; z0, z0, z0, z0, z0, z1],
  !![z1, z0, z0, z0, z0, z0; z0, z1, z0, z0, z0, z0; z0, z0, z1, z0, z0, z0; z0, z0, z0, z1, w2, w2; z0, z0, z0, w, w2, w; z0, z0, z0, w, w, w2],
  !![z1, z0, z0, z0, z0, z0; z0, z1, z0, z0, z0, z0; z0, z0, z1, z0, z0, z0; z0, z0, z0, z1, w2, w; z0, z0, z0, z1, z1, z1; z0, z0, z0, z1, w, w2]
]

@[expose] def nativeInv (i : Fin 18) : Matrix (Fin 6) (Fin 6) F4c :=
  ((nativeGen i).map F4c.sg).transpose

@[expose] def evalNative (w : List (Fin 18 × Bool)) : Matrix (Fin 6) (Fin 6) F4c :=
  (w.map fun p => if p.2 then nativeGen p.1 else nativeInv p.1).prod

theorem nativeGen_mul_nativeInv : ∀ i, nativeGen i * nativeInv i = 1 := by decide +kernel

theorem nativeInv_mul_nativeGen : ∀ i, nativeInv i * nativeGen i = 1 := by decide +kernel

theorem nativeGen_det : ∀ i, (nativeGen i).det = 1 := by decide +kernel

theorem nativeRels : ∀ w ∈ relsP, evalNative w = 1 := by decide +kernel

theorem nativeComm_edge_one_four :
    ∀ a ∈ ([10, 11] : List (Fin 18)), ∀ b ∈ ([16, 17] : List (Fin 18)),
      nativeGen a * nativeGen b = nativeGen b * nativeGen a := by decide +kernel

end CFSG.StandardType.QTwo.SixPoint

end
