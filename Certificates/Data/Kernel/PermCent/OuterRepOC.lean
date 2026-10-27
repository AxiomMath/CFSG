module

public import Certificates.Data.Kernel.PermCent.OuterRepC

public section

namespace CFSG.Certificates.Kernel.PkCV.OutR

variable {n : Nat} [Small n]

@[expose] noncomputable def sqOT (inP : CV n → Bool) (LS gs : List (CV n)) (ψ : CV n) : Bool :=
  inP ψ || sqT LS gs ψ

@[expose] noncomputable def conj4KC (LS refs ks : List (CV n)) : Bool :=
  LS.all fun a => !(powOneC a 4 && !powOneC a 2) ||
    (refs.any fun c => powOneC c 3 && eq22C c (a * a) (a * a) c && !eq22C c a a c) ||
    ks.any fun k => inC LS (k⁻¹ * a * k) && fixC LS (k⁻¹ * a * k)

@[expose] noncomputable def passO (inP : CV n → Bool) (LA LS gs csO csI : List (CV n))
    (τ v : CV n) : Bool :=
  LA.all fun ψ => outT csO τ ψ && innerT csI v ψ && centT LS gs ψ && sqOT inP LS gs ψ

end CFSG.Certificates.Kernel.PkCV.OutR

end
