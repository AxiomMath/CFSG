module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.A8Coord

open Certificates.A8Nbr476 CFSG.Assembly CFSG.StandardType Matrix

@[expose] def a8SignThree : M4 := Matrix.diagonal ![1, 1, 1, -1]

@[expose] def GGA8LFrameB {G : Type} [Group G] (Bs L J : Subgroup G) (xb : ↥Bs)
    (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) : Prop :=
  ι (Additive.ofMul xb) = Pi.single 0 1 ∧
    (∀ σ : Equiv.Perm (Fin 4), σ 0 = 0 → ∃ ψ ∈ ggAutomizer J Bs, ∀ b : ↥Bs,
      ι (Additive.ofMul (ψ b)) = vecMul (ι (Additive.ofMul b)) (a8PermMat σ)) ∧
    ∃ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs,
      ι (Additive.ofMul (ψ b)) = vecMul (ι (Additive.ofMul b)) a8SignThree

@[expose] def GGA8LSideB {G : Type} [Group G] (Bs D L J : Subgroup G) (xb : ↥Bs) : Prop :=
  Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D ∧ (∃ w ∈ J, orderOf w = 73) ∧
    ∃ ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7), GGA8LFrameB Bs L J xb ι

end CFSG.StandardType.A8Coord

end
