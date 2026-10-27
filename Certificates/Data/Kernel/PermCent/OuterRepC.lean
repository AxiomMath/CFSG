module

public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.Certificates.Kernel.PkCV.OutR

variable {n : Nat} [Small n]

@[expose] noncomputable def fixC (cs : List (CV n)) (ψ : CV n) : Bool :=
  cs.all fun c => eq22C ψ c c ψ

@[expose] noncomputable def inC (L : List (CV n)) (x : CV n) : Bool :=
  L.any fun s => decide (s = x)

@[expose] noncomputable def sub3C (cs : List (CV n)) (τ : CV n) : Bool :=
  cs.all fun c => powOneC c 3 && eq22C c τ τ c

@[expose] noncomputable def outT (csO : List (CV n)) (τ ψ : CV n) : Bool :=
  !fixC csO ψ || decide (ψ = 1) || decide (ψ = τ)

@[expose] noncomputable def innerT (csI : List (CV n)) (v ψ : CV n) : Bool :=
  !fixC csI ψ || ((decide (ψ * ψ = 1) || decide (ψ * ψ = v)) &&
    (!decide (ψ * ψ = 1) || decide (ψ = 1) || decide (ψ = v)))

@[expose] noncomputable def cycT (csI pl : List (CV n)) (ψ : CV n) : Bool :=
  !fixC csI ψ || inC pl ψ

@[expose] noncomputable def centT (LS gs : List (CV n)) (ψ : CV n) : Bool :=
  !fixC gs ψ || inC LS ψ

@[expose] noncomputable def sqT (LS gs : List (CV n)) (ψ : CV n) : Bool :=
  !(!decide (ψ * ψ = 1) && decide (ψ * ψ * (ψ * ψ) = 1) && inC LS (ψ * ψ) &&
      gs.all fun q => inC LS (ψ * q * ψ⁻¹)) || fixC gs (ψ * ψ)

@[expose] noncomputable def passA (LA LS gs csO csI pl : List (CV n)) (τ v : CV n) : Bool :=
  LA.all fun ψ => outT csO τ ψ && innerT csI v ψ && cycT csI pl ψ && centT LS gs ψ && sqT LS gs ψ

@[expose] noncomputable def bangC (τ l c₁ c₂ : CV n) : Bool :=
  powOneC c₁ 3 && powOneC c₂ 3 && !decide (c₁ = 1) && !decide (c₂ = 1) && eq22C c₁ τ τ c₁ &&
    eq22C c₂ τ τ c₂ && powOneC (c₁ * c₂) 2 && !decide (c₁ * c₂ = 1) &&
    decide (τ * l * τ⁻¹ * l⁻¹ = c₁ * c₂)

@[expose] noncomputable def wordWC (s0 a b : CV n) : Bool :=
  powOneC a 3 && powOneC b 3 && !decide (a = 1) && !decide (b = 1) && eq22C a s0 s0 a &&
    eq22C b s0 s0 b && decide (a * b * (a * b) * (a * b) = s0)

@[expose] noncomputable def conj4C (LS refs : List (CV n)) : Bool :=
  LS.all fun a => !(powOneC a 4 && !powOneC a 2) ||
    refs.any fun c => powOneC c 3 && eq22C c (a * a) (a * a) c && !eq22C c a a c

end CFSG.Certificates.Kernel.PkCV.OutR

end
