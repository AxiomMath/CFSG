module

public import Certificates.Data.Kernel.PermCent.CV
public import Certificates.Data.OmegaT0
public import Certificates.Data.OmegaCentK

public section

namespace CFSG.Certificates.Kernel.PkCV.P45T

open CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] noncomputable def sylowC : Bool :=
  let T := elemsC QT0
  decide ((T.filter fun g => T.all fun t => eq22C g t t g).length = 2) &&
    (elemsC QA45).all fun a => !(T.all fun t => eq22C a t t a) || decide (a ∈ T)

@[expose] noncomputable def coverC (reps L : List (CV 45)) : Bool :=
  L.all fun t => !(powOneC t 2 && !decide (t = 1)) ||
    L.any fun g => reps.any fun r => eq22C g t r g

@[expose] noncomputable def cntCentC (L : List (CV 45)) (r : CV 45) : Nat :=
  (L.filter fun g => eq22C g r r g).length

@[expose] noncomputable def n7C : Bool :=
  let L0 := elemsC QP45
  let T := elemsC QT0
  let z := cOf (Certificates.OmegaT0.z0 ())
  let y := cOf (Certificates.OmegaT0.yB ())
  let a := cOf (Certificates.OmegaT0.za ())
  let b := cOf (Certificates.OmegaT0.zb ())
  let c := cOf (Certificates.OmegaT0.ya ())
  let d := cOf (Certificates.OmegaT0.yb ())
  coverC [z, y] L0 && decide (z ∈ T) && decide (y ∈ T) &&
    decide (cntCentC L0 z = 576) && decide (cntCentC T z = 64) &&
    decide (cntCentC L0 y = 96) && decide (cntCentC T y = 32) &&
    decide (a ∈ T) && decide (b ∈ T) && eq22C a z z a && eq22C b z z b &&
    decide (a * b * a⁻¹ * b⁻¹ = z) &&
    decide (c ∈ T) && decide (d ∈ T) && eq22C c y y c && eq22C d y y d &&
    decide (c * d * c⁻¹ * d⁻¹ = y)

@[expose] noncomputable def centKC : Bool :=
  let t := cOf (Certificates.P43Twin.tA ())
  let O := ((elemsC QP45).filter fun g => eq22C g t t g).filter fun x => powOneC x 9
  (elemsC QA45).all fun a => !(O.all fun x => eq22C a x x a) || decide (a = 1) || decide (a = t)

end CFSG.Certificates.Kernel.PkCV.P45T

end
