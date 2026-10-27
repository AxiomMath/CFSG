module

public import CFSG.LocalAnalysis.StandardType.GGQTwoHeartJInput
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

structure GGHeartDict {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) where
  e : Fin 6 ≃ M.Λ
  Ψ : M.V →ₗ[ZMod 3] E6Heart.H
  cartan_eq : ∀ i j, M.cartan (e i) (e j) = E6Heart.C i j
  surj : Function.Surjective Ψ
  ker_eq : LinearMap.ker Ψ = Submodule.span (ZMod 3) {M.xV}
  form_eq : ∀ (a : M.Λ → ℤ) (v : M.V),
    M.rootForm a v = E6Heart.alpha (fun i => a (e i)) (Ψ v)

end CFSG.StandardType

end
