module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSL

public section

namespace CFSG.StandardType

open Polynomial CoordSL Multiplicative
open scoped MatrixGroups

variable {G : Type} [Group G]

@[expose] def ggSecFiveBPermQTwoCoords {Bs : Subgroup G} {n r : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (π : Fin (r + 2) ≃ Fin n) (b : ↥Bs) :
    Multiplicative (Fin (r + 1) → ZMod 3) :=
  ofAdd fun k => toAdd (eta b (π k.succ))

@[expose] def GGSecFiveBPermQTwoKFrame (Bs K : Subgroup G) {n r m d : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (π : Fin (r + 2) ≃ Fin n)
    {g : (ZMod 2)[X]} [Fact (Irreducible g)]
    (ε : Fin m ≃ (Fin (rootPB g).dim × Fin (r + 1)) ⊕ Fin d) (hC : (rootMat g).det = 1)
    (hCp : rootMat g ^ 3 = 1) (κ : SL(m, ZMod 2) →* G) : Prop :=
  Function.Injective κ ∧ κ.range = K ∧ g ∣ cyclotomic 3 (ZMod 2) ∧
    ∀ (b : ↥Bs) (u : SL(m, ZMod 2)), (b : G) * κ u * (b : G)⁻¹ =
      frameHom κ 1 ε hC hCp (ggSecFiveBPermQTwoCoords eta π b) * κ u *
        (frameHom κ 1 ε hC hCp (ggSecFiveBPermQTwoCoords eta π b))⁻¹

end CFSG.StandardType

end
