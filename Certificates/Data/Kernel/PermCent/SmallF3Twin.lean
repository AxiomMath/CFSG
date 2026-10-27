module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.Certificates.Kernel.PkCV.SmallF3T

variable {n : Nat} [Small n]

@[expose] noncomputable def c6freeC (LA LP : List (CV n)) : Bool :=
  let LI := LA.filter fun τ => powOneC τ 2
  (LP.filter fun y => powOneC y 2 && !decide (y = 1)).all fun y =>
    (LP.filter fun u => powOneC u 3 && !decide (u = 1) && eq22C y u u y).all fun u =>
      LI.all fun τ =>
        bif eq22C τ y y τ && eq22C τ u u τ then decide (τ = 1) || decide (τ = y) else true

@[expose] noncomputable def fhO3C (LA LP : List (CV n)) : Bool :=
  let LU := LP.filter fun u => powOneC u 3 && !decide (u = 1)
  (LA.filter fun τ => powOneC τ 2).all fun τ =>
    let LC := LP.filter fun c => eq22C τ c c τ
    (LU.filter fun u => eq22C τ u u τ).all fun u =>
      LC.any fun c => !powOneC (u * (c * u * c⁻¹)) 27

@[expose] noncomputable def centListC (L : List (CV n)) (s : CV n) : List (CV n) :=
  L.filter fun g => eq22C g s s g

@[expose] noncomputable def invListC (L : List (CV n)) : List (CV n) :=
  L.filter fun g => powOneC g 2 && !decide (g = 1)

@[expose] noncomputable def cent48C (LP : List (CV n)) : Bool :=
  (invListC LP).all fun s => decide ((centListC LP s).length = 48)

@[expose] noncomputable def order13PairC (Cs Cb : List (CV n)) : Bool :=
  Cs.any fun c₁ => Cb.any fun c₂ => powOneC (c₁ * c₂) 13 && !decide (c₁ * c₂ = 1)

@[expose] noncomputable def order13C (LA LP : List (CV n)) : Bool :=
  let I := invListC LA
  I.all fun s =>
    let Cs := centListC LP s
    bif decide (Cs.length = 48) then
      I.all fun b => bif !decide (b = s) && eq22C b s s b then
        order13PairC Cs (centListC LP b) else true
    else true

@[expose] noncomputable def fourGenC (LA LP : List (CV n)) : Bool :=
  cent48C LP && order13C LA LP

@[expose] noncomputable def cent3OddAllC (LA LP : List (CV 28)) : Bool :=
  LP.all fun g => !(decide (g * g * g = 1) && !decide (g = 1)) ||
    (LP.filter fun x => eq22C g x x g).length % 2 == 1 ||
    LA.all fun σ => !(powOneC σ 2 && eq22C σ g g σ) || siftC CFSG.GH74.KGroups.U33.QP σ 0

end CFSG.Certificates.Kernel.PkCV.SmallF3T

end
