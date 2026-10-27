module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordCase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Certificates.A8Nbr476

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGForkA8CoordC3Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → p = 7 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1 →
        GGHasLabel ⟨.C, 3, 3⟩ (L ⧸ Subgroup.center L) →
        ∃ (c : Case) (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)), c ∈ allCases ∧
          (∀ k : Fin 6, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
            ι (Additive.ofMul (φ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (gens c k)) ∧
          (c.1 = true → StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3)

@[expose] def GGForkA8Coord2D4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → p = 7 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1 →
        GGHasLabel ⟨.twD, 4, 3⟩ (L ⧸ Subgroup.center L) →
        ∃ (c : Case) (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)), c ∈ allCases ∧
          (∀ k : Fin 6, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
            ι (Additive.ofMul (φ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (gens c k)) ∧
          (c.1 = true → StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3)

theorem ggForkA8CoordRestInput_of_split (hC : GGForkA8CoordC3Input)
    (hD : GGForkA8Coord2D4Input) : GGForkA8CoordRestInput :=
  fun G _ _ p B Bs x L D J h1 h2 h3 hp y K hK hKm hL =>
    hL.elim (hC G p B Bs x L D J h1 h2 h3 hp y K hK hKm)
      (hD G p B Bs x L D J h1 h2 h3 hp y K hK hKm)

end CFSG.StandardType

end
