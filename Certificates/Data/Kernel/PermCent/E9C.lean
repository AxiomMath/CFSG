module

public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.Certificates.Kernel.PkCV.E9

@[expose] noncomputable def nineC (a b : CV 26) : List (CV 26) :=
  [1, a, a ^ 2, b, a * b, a ^ 2 * b, b ^ 2, a * b ^ 2, a ^ 2 * b ^ 2]

@[expose] noncomputable def stabC (L : List (CV 26)) (t f : CV 26) : List (CV 26) :=
  L.filter fun c => eq22C c t t c && (eq22C c f f c || eq22C c f (f ^ 2) c)

@[expose] noncomputable def e9C (L : List (CV 26)) (t a b : CV 26) : Bool :=
  decide (t ∈ L) && powOneC t 2 && !decide (t = 1) && decide (nineC a b).Nodup &&
    (nineC a b).all (fun x => decide (x ∈ L) && eq22C t x x⁻¹ t &&
      decide (x⁻¹ ∈ nineC a b) && (nineC a b).all fun y => decide (x * y ∈ nineC a b)) &&
    L.all (fun c => !eq22C c t t c ||
      (nineC a b).all fun x => decide (c * x * c⁻¹ ∈ nineC a b)) &&
    (nineC a b).all fun f => decide (f = 1) || decide ((stabC L t f).length ≤ 12)

end CFSG.Certificates.Kernel.PkCV.E9

end
