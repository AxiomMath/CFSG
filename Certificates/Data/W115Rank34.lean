module

public import Certificates.Data.SmithB45MatM22Mod

public section

namespace CFSG.Quasithin.B45Mat.M22

open CFSG.Sporadic.Mathieu CFSG.Quasithin.H.Mathieu

@[expose] def tab34P (p : Equiv.Perm (Fin 22)) : Vector (Vector (ZMod 2) 34) 34 :=
  let t := maskTab 10 (actC10 (psiArr p))
  mulT (mulT P34 (kronTab t t)) B34

@[expose] def subIdT {n : ℕ} (A : Vector (Vector (ZMod 2) n) n) : Vector (Vector (ZMod 2) n) n :=
  Vector.ofFn fun i => Vector.ofFn fun j => (A.get i).get j - if i = j then 1 else 0

@[expose] def w115Delta : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 13] * List.formPerm [1, 4] * List.formPerm [2, 3] * List.formPerm [5, 18] *
    List.formPerm [6, 10] * List.formPerm [7, 12] * List.formPerm [8, 11] *
    List.formPerm [9, 21] * List.formPerm [14, 19] * List.formPerm [15, 20] *
    List.formPerm [16, 17]

@[expose] def w115R2 : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21] * List.formPerm [1, 16] * List.formPerm [3, 18] * List.formPerm [5, 14] *
    List.formPerm [7, 8] * List.formPerm [12, 17] * List.formPerm [15, 19]

@[expose] def w115Y : Equiv.Perm (Fin 22) := m22gB * m22gA * m22gB

@[expose] def w115HA : Equiv.Perm (Fin 22) := m22gA * (w115Y * m22gA * w115Y⁻¹)

@[expose] def w115HD : Equiv.Perm (Fin 22) := w115Delta * (w115Y * w115Delta * w115Y⁻¹)

@[expose] def w115HR : Equiv.Perm (Fin 22) := w115R2 * (m22gA * w115R2 * m22gA⁻¹)

@[expose] def w115PARows : List ℕ :=
  [6260781, 4927926, 325470, 22695395, 51323648, 21696040, 35301493, 52322419, 21951827, 22758342,
    21641105, 22638966, 51647899, 325498, 33745559, 38657225, 22567250, 15106, 5043914, 22033458,
    22985361, 5587589, 1740599, 21700617]

@[expose] def w115PA : Vector (Vector (ZMod 2) 34) 24 :=
  decF2 24 34 w115PARows

@[expose] def w115QARows : List ℕ :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
    262144, 524288, 1048576, 2097152, 4194304, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def w115QA : Vector (Vector (ZMod 2) 24) 34 :=
  decF2 34 24 w115QARows

@[expose] def w115PDRows : List ℕ :=
  [168178573, 168717274, 35990682, 10116538, 142769615, 35862364, 10947070, 142769614, 10947772,
    168717464, 168718298, 35127359, 11087820, 145836570, 135816503, 179248337, 3303221, 3883012,
    146566104, 170475526, 179321224, 3751940, 33685504, 10616832]

@[expose] def w115PD : Vector (Vector (ZMod 2) 34) 24 :=
  decF2 24 34 w115PDRows

@[expose] def w115QDRows : List ℕ :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
    262144, 524288, 1048576, 2097152, 4194304, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0]

@[expose] def w115QD : Vector (Vector (ZMod 2) 24) 34 :=
  decF2 34 24 w115QDRows

@[expose] def w115PRRows : List ℕ :=
  [33710593, 36145560, 7368935, 43850143, 46301430, 37970827, 43934680, 37813182, 49121946,
    41029863, 40987367, 33645061, 41054946, 7360743, 210944, 7600354, 40921831, 44395390,
    35320265, 40732752, 34010009, 12444265, 41050850, 28677]

@[expose] def w115PR : Vector (Vector (ZMod 2) 34) 24 :=
  decF2 24 34 w115PRRows

@[expose] def w115QRRows : List ℕ :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 0, 131072,
    262144, 524288, 1048576, 2097152, 0, 0, 4194304, 8388608, 0, 0, 0, 0, 0, 0, 0]

@[expose] def w115QR : Vector (Vector (ZMod 2) 24) 34 :=
  decF2 34 24 w115QRRows

end CFSG.Quasithin.B45Mat.M22
