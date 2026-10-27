module

public import CFSG.Quasithin.Background.Harris.R1.D4VertPres
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

public section

namespace CFSG.Quasithin.Background.Harris.R1

open D4Vert

@[expose] def l28Borel {X : Type*} [Group X] (a b : X) : Subgroup X :=
  Subgroup.closure {evalWord ![a, b] l28U, evalWord ![a, b] l28C}

@[expose] def L28BorelModel : Prop :=
  ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3),
    (∀ r ∈ l28Rels, evalWord ![a, b] r = 1) ∧ Subgroup.closure ({a, b} : Set _) = ⊤ ∧
    Nat.card (l28Borel a b) = 56 ∧
    (∃ E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)),
      Nat.card E = 8 ∧ Subgroup.normalizer (E : Set _) = l28Borel a b) ∧
    a ∉ l28Borel a b ∧
    ∀ i j : Fin 9, i ≠ j →
      (evalWord ![a, b] (l28H.getD i []))⁻¹ * evalWord ![a, b] (l28H.getD j []) ∉ l28Borel a b

end CFSG.Quasithin.Background.Harris.R1
