module

public import Certificates.Data.Kernel.PermCent.Sp6BTwin
public import Certificates.Data.E4QuatSp6Good

public section

namespace CFSG.Certificates.Kernel.PkCV.Sp6E

open CFSG.EvenSmallLie.Sp6 CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.Certificates.Kernel.PkCV.Sp6B

@[expose] noncomputable def r2C : CV 36 := cOf sp6Rep2

@[expose] noncomputable def iC : CV 36 := cOf (rho ())

@[expose] noncomputable def jC : CV 36 := cOf (jay ())

@[expose] noncomputable def ngWitC : List (CV 36) := (ngWit ()).map cOf

@[expose] noncomputable def E2 : List (CV 36) := elemsC sp6CentQ2

@[expose] noncomputable def normsC (L : List (CV 36)) (i j h : CV 36) : Bool :=
  decide (h * i * h⁻¹ ∈ L) && decide (h * j * h⁻¹ ∈ L)

@[expose] noncomputable def ngT (E L : List (CV 36)) (r j : CV 36) (ys : List (CV 36)) : Bool :=
  ys.all (fun y => decide (y ^ 3 = 1) && decide (y * r = r * y) && decide (y * j = j * y)) &&
    E.all fun c => !(normsC L r j c && !(decide (c * r = r * c) && decide (c * j = j * c)) &&
      ys.all (fun y => decide (c * y = y * c)) && decide (c ^ 9 = 1))

@[expose] noncomputable def ngC : Bool := ngT E2 L0C iC jC ngWitC

@[expose] noncomputable def sigT (E : List (CV 36)) (i j i1 j1 : CV 36) (L1 : List (CV 36)) : Bool :=
  E.all fun g => !(decide (g * g = 1) && decide (g * i = i * g) && decide (g * j = j * g) &&
    L1.any fun w => !decide (w * w = 1) && decide (g * i1 * g * w = w * i1) &&
      decide (g * j1 * g * w = w * j1))

@[expose] noncomputable def sigC : Bool :=
  let t := wsC.getD 11 1
  sigT E2 iC jC (t * iC * t⁻¹) (t * jC * t⁻¹) L1C

@[expose] noncomputable def centSqT (E : List (CV 36)) (i j i1 j1 : CV 36) : Bool :=
  E.all fun g => !(decide (g * i = i * g) && decide (g * j = j * g) && decide (g * i1 = i1 * g) &&
    decide (g * j1 = j1 * g) && !decide (g * g = 1))

@[expose] noncomputable def centSqC : Bool :=
  let t := wsC.getD 11 1
  centSqT E2 iC jC (t * iC * t⁻¹) (t * jC * t⁻¹)

@[expose] noncomputable def moveT (E : List (CV 36)) (r i j : CV 36) : Bool :=
  (E.filter fun a => decide (a * a = 1 ∧ a ≠ 1 ∧ a ≠ r ∧ a * i = i * a ∧ a * j = j * a)).all
    fun a => (E.filter fun c => decide (c * c * c = 1)).any fun c => decide (c * a ≠ a * c)

@[expose] noncomputable def moveC : Bool := moveT E2 r2C iC jC

@[expose] noncomputable def commGensC (i j b : CV 36) : Bool :=
  decide (b * i = i * b) && decide (b * j = j * b)

@[expose] noncomputable def goodWitC (r i j t x : CV 36) : Bool :=
  commGensC i j (x⁻¹ * (r * t) * x) && commGensC i j ((x * t)⁻¹ * (r * t) * (x * t))

@[expose] noncomputable def tT (L : List (CV 36)) (r i j : CV 36) (T X : List (CV 36)) : Bool :=
  T.all fun w => !(decide (w * r * w⁻¹ * r = r * (w * r * w⁻¹)) && !normsC L i j (w * r * w⁻¹)) ||
    X.any fun x => goodWitC r i j (w * r * w⁻¹) x

@[expose] noncomputable def tC : Bool := tT L0C r2C iC jC wsC wsC

end CFSG.Certificates.Kernel.PkCV.Sp6E

end
