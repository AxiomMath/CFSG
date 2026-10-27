module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.LargeExtraspecial.AS35YRU33Data
public import CFSG.LargeExtraspecial.AS35YSU33Data
public import CFSG.LargeExtraspecial.S63CU33Inputs
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Check

public section

namespace CFSG.Certificates.Kernel.PkCV.U33T

open CFSG.GH74.KGroups.U33

@[expose] noncomputable def invConjC : Bool :=
  (elemsC QP).all fun g => !decide (g * g = 1) || decide (g = 1) ||
    (elemsC QP).any fun c => decide (c * g * c⁻¹ = cOf CFSG.LargeExtraspecial.AS35YR.u33d0)

@[expose] noncomputable def elemAt (C : List (CV 28)) (d e : CV 28) : Bool :=
  decide (e = 1) || decide (e = d) || !decide (e * d = d * e) ||
    C.any fun c => !decide (e * (c * e * c⁻¹) = c * e * c⁻¹ * e)

@[expose] noncomputable def elemC : Bool :=
  (elemsC QP).all fun d => !decide (d * d = 1) || decide (d = 1) ||
    (((elemsC QA).filter fun e => decide (e * e = 1)).all
      (elemAt ((elemsC QP).filter fun c => decide (c * d = d * c)) d))

@[expose] noncomputable def twoC (x : CV 28) : Bool := decide (x ^ 32 = 1)

@[expose] noncomputable def centC (L : List (CV 28)) (s : CV 28) : List (CV 28) :=
  L.filter fun c => decide (c * s = s * c)

@[expose] noncomputable def coreC (C : List (CV 28)) : List (CV 28) :=
  let C3 := C.filter fun c => decide (c ^ 3 = 1)
  C.filter fun x => twoC x && C3.all fun c => twoC (x * (c * x * c⁻¹))

@[expose] noncomputable def invCheckC (L : List (CV 28)) (s : CV 28) : Bool :=
  let C := centC L s
  let P := coreC C
  P.length == 16 &&
  C.all (fun t => !decide (t * t = 1) || P.any fun p => decide (p = t)) &&
  P.any fun q => decide (q * q = s) && C.all (fun c => decide (q * c = c * q)) &&
    P.all fun n => !(P.all fun m => decide (n * m = m * n)) ||
      [1, q, q * q, q * q * q].any fun r => decide (r = n)

@[expose] noncomputable def centAtC (s : CV 28) : Bool :=
  !decide (s * s = 1) || decide (s = 1) || invCheckC (elemsC QP) s

@[expose] noncomputable def invsOfC (L : List (CV 28)) : List (CV 28) :=
  L.filter fun s => s * s == 1 && s != 1

@[expose] noncomputable def o3OfC (L : List (CV 28)) : List (CV 28) :=
  L.filter fun x => x ^ 3 == 1 && x != 1

@[expose] noncomputable def centerC : Bool :=
  (elemsC QP).all fun g => !(g * cOf pa == cOf pa * g && g * cOf pb == cOf pb * g) || g == 1

@[expose] noncomputable def expC : Bool :=
  (elemsC QP).all fun x => !(x ^ 27 == 1) || x ^ 3 == 1

@[expose] noncomputable def f1C (L I : List (CV 28)) : Bool :=
  L.all fun g => !(g ^ 7 == 1 && g != 1) || I.all fun s => !(g * s == s * g)

@[expose] noncomputable def f3C (I O : List (CV 28)) : Bool :=
  O.all fun g => O.all fun h =>
    !(g * h == h * g && h != g && h != g * g) ||
      [g, h, g * h, g * h * h].any fun x => I.all fun s => !(x * s == s * x)

@[expose] noncomputable def x5gC (Cg I : List (CV 28)) (g : CV 28) : Bool :=
  I.all fun s => !(g * s == s * g) ||
    Cg.any fun c => (s * (c * s * c⁻¹)) ^ 3 == 1 && s * (c * s * c⁻¹) != 1

@[expose] noncomputable def x5C (L I O : List (CV 28)) : Bool :=
  O.all fun g => if I.any (fun s => g * s == s * g) then
    x5gC (L.filter (fun c => g * c == c * g)) I g else true

@[expose] noncomputable def closureStepC (gs L : List (CV 28)) : List (CV 28) :=
  (L ++ L.flatMap fun x => gs.map fun g => x * g).dedup

@[expose] noncomputable def t0LC : List (CV 28) :=
  (List.range 40).foldl (fun L _ => closureStepC
    [cOf CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin.ta,
      cOf CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin.tb] L) [1]

@[expose] noncomputable def t0C : Bool :=
  let T := t0LC
  let P := elemsC QP
  T.length == 32 && decide T.Nodup && T.contains 1 &&
    T.all (fun x => T.contains x⁻¹ && P.contains x && T.all fun y => T.contains (x * y))

@[expose] noncomputable def zC : Bool :=
  let T := t0LC
  let z := cOf CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin.z0
  T.contains z && z ^ 4 == 1 && z ^ 2 != 1 && T.all (fun x => x * z == z * x) &&
    T.all (fun x => !(T.all fun y => x * y == y * x) || [1, z, z ^ 2, z ^ 3].contains x)

@[expose] noncomputable def cC : Bool :=
  ((elemsC QP).filter fun x =>
    x * cOf CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin.z0 ^ 2 ==
      cOf CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin.z0 ^ 2 * x).length == 96

@[expose] noncomputable def e1C : Bool :=
  let T := t0LC
  let z := cOf CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin.z0
  let t := z ^ 2
  (elemsC QP).all fun g =>
    !(g ^ 3 == 1 && g != 1 && g * t == t * g) ||
      T.all fun x => !(x * g == g * x) || [1, z, z ^ 2, z ^ 3].contains x

@[expose] noncomputable def centBlk (j : Nat) : Bool :=
  (((elemsC QP).drop (j * 756)).take 756).all centAtC

end CFSG.Certificates.Kernel.PkCV.U33T

end
