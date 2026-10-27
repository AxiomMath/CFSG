module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK65
public import CFSG.GH74.KGroups.Sz8DInputs

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5129

open CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8 CFSG.GH74.KGroups.Sz8D CFSG.Certificates.Kernel.PkEnum

@[expose] noncomputable def xsC : Fin 3 → CV 65 := ![cOf xA, cOf xB, cOf xC]

@[expose] noncomputable def ysC : Fin 3 → CV 65 := ![cOf yA, cOf yB, cOf yC]

@[expose] noncomputable def syC : List (CV 65) := [sy0, sy1, sy2, sy3, sy4, sy5].map cOf

@[expose] noncomputable def wP : CV 65 := cOf pa * cOf pb * cOf pa

@[expose] noncomputable def sig0 : CV 65 := wP * cOf sg0 * wP⁻¹

@[expose] def s3 (f : Fin 3 → ZMod 2) : ZMod 2 := f 0 + f 1 + f 2

@[expose] def qOf (qv : List (Fin 3 → ZMod 2)) (a : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  qv.getD ((a 0).val + 2 * (a 1).val + 4 * (a 2).val) 0

@[expose] noncomputable def conjOK (g : CV 65) (M W N : Fin 3 → Fin 3 → ZMod 2) : Bool :=
  (List.finRange 3).all (fun i =>
      eq22C g (xsC i) (pr3 xsC (fun k => M k i) * pr3 ysC (W i)) g) &&
    (List.finRange 3).all fun j => eq22C g (ysC j) (pr3 ysC (fun l => N l j)) g

@[expose] noncomputable def sqOK (qv : List (Fin 3 → ZMod 2)) : Bool :=
  allVec3.all fun a => eq22C (pr3 xsC a) (pr3 xsC a) (pr3 ysC (qOf qv a)) 1

@[expose] def invB (M N u : Fin 3 → Fin 3 → ZMod 2) : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j =>
    decide (u i j = s3 fun k => s3 fun l => M k i * N l j * u k l)

@[expose] def cycB (qv : List (Fin 3 → ZMod 2)) (u : Fin 3 → Fin 3 → ZMod 2) : Bool :=
  allVec3.all fun a => decide ((s3 fun i => s3 fun j => a i * qOf qv a j * u i j) = 0)

@[expose] def zeroB (u : Fin 3 → Fin 3 → ZMod 2) : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j => decide (u i j = 0)

@[expose] def kAlgB (M₁ N₁ M₂ N₂ : Fin 3 → Fin 3 → ZMod 2) (qv : List (Fin 3 → ZMod 2)) : Bool :=
  allU.all fun u => !(invB M₁ N₁ u && invB M₂ N₂ u && cycB qv u) || zeroB u

@[expose] noncomputable def orbOK (c o : Nat) : Bool :=
  (elemsC QS).all (fun s => img 65 s.1 c == c) &&
    (List.range 65).all fun i => i == c || (elemsC QS).any fun s => img 65 s.1 o == i

@[expose] noncomputable def ysCentOK : Bool :=
  (List.finRange 3).all fun j => syC.all fun c => eq22C (ysC j) c c (ysC j)

@[expose] noncomputable def commOK : Bool :=
  syC.all fun a => syC.all fun b => syC.all fun c =>
    eq22C (a * b * a⁻¹ * b⁻¹) c c (a * b * a⁻¹ * b⁻¹)

@[expose] def isZ (a : Fin 3 → ZMod 2) : Bool := a 0 == 0 && a 1 == 0 && a 2 == 0

@[expose] noncomputable def ncOK : Bool :=
  allVec3.all fun a => isZ a ||
    (List.finRange 3).any fun i => !eq22C (pr3 xsC a) (xsC i) (xsC i) (pr3 xsC a)

@[expose] noncomputable def decOK : Bool :=
  decide ((allVec3.flatMap fun a => allVec3.map fun b => (pr3 xsC a * pr3 ysC b).1).Nodup)

@[expose] noncomputable def normSOK (g : CV 65) : Bool :=
  syC.all fun c => siftC QS (g * c * g⁻¹) 0

end CFSG.Certificates.Kernel.PkCV.KGrp.K5129

end
