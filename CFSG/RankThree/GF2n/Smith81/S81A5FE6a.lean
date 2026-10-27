module

public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type*} [Field K]

theorem rho_one : rho K 1 = 1 :=
  map_one (TauCeti.extPowerRep K 6 3)

theorem rho_mul_apply (g h : GL (Fin 6) K) (ξ : Cube K) :
    rho K (g * h) ξ = rho K g (rho K h ξ) := by
  rw [rho_mul, Module.End.mul_apply]

end CFSG.RankThree.GF2n.Smith81.A5Cube
