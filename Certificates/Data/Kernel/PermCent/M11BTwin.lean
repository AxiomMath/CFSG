module

public import Certificates.Data.Kernel.PermCent.SmallB
public import Certificates.Data.M11Sylow3
public import Certificates.Data.SmithB45ExcM11Check

public section

namespace CFSG.Certificates.Kernel.PkCV.M11B

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] noncomputable def E : List (CV 11) := elemsC m11Certificate

@[expose] noncomputable def A : CV 11 := cOf m11gA

@[expose] noncomputable def B : CV 11 := cOf m11gB

@[expose] noncomputable def wordC : Bool := orderIsP (A * B * A * B⁻¹ * A * B * B) 5 [5]

@[expose] noncomputable def pairCntC : Nat :=
  ((E.filter (orderIsP · 2 [2]) ×ˢ E.filter (orderIsP · 4 [2])).filter
    fun q => orderIsP (q.1 * q.2) 11 [11] && orderIsP (q.1 * q.2 * q.1⁻¹ * q.2⁻¹) 6 [2, 3] &&
      orderIsP (q.1 * q.2 * q.1 * q.2⁻¹ * q.1 * q.2 * q.2) 5 [5]).length

@[expose] noncomputable def o4C : Bool :=
  (E.filter (orderIsP · 2 [2])).all fun y => !(y * A == A * y) || y == A ||
    E.any fun g => g * A == A * g &&
      (orderIsP (y * (g * y * g⁻¹)) 4 [2] || orderIsP (y * (g * y * g⁻¹)) 8 [2])

@[expose] noncomputable def U : CV 11 := cOf (M11Sylow.pU ())

@[expose] noncomputable def V : CV 11 := cOf (M11Sylow.pV ())

@[expose] noncomputable def EL : List (CV 11) := (M11Sylow.pE ()).map cOf

@[expose] noncomputable def centC : Bool :=
  E.all fun g => !(decide (g * U = U * g) && decide (g * V = V * g)) || decide (g ∈ EL)

@[expose] noncomputable def cent18C : Bool :=
  EL.all fun e => decide (e = 1) || (E.filter fun g => decide (g * e = e * g)).length == 18

@[expose] noncomputable def moveC : Bool :=
  E.all fun g => !(orderIsP g 5 [5] || orderIsP g 11 [11]) ||
    ((ev g M11Sylow.p0 != M11Sylow.p0 && ev g M11Sylow.p0 != M11Sylow.q0) ||
      (ev g M11Sylow.q0 != M11Sylow.p0 && ev g M11Sylow.q0 != M11Sylow.q0))

end CFSG.Certificates.Kernel.PkCV.M11B

end
