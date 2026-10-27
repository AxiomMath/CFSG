module

public import CFSG.LocalAnalysis.StandardType.GGHalfStageADefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

structure GGHalfWeylCtx {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (m : ℕ) (y : G) (K : Subgroup G) : Prop where
  cfg : GGConfig p B Bs x L D J
  inn : GGInnerDiagAll p B Bs x L D J
  nbr : GGTypeAHalfNbr p B Bs x L D J (m + 1 + 1) y K
  hJK : J ≤ K

@[expose] def GGHalfActsAs {G : Type} [Group G] {N : ℕ} (X : Subgroup G)
    (ψ : SpecialLinearGroup (Fin (N + 1)) F2 →* G) (b : G)
    (t : SpecialLinearGroup (Fin (N + 1)) F2) : Prop :=
  ∀ l ∈ X, b * l * b⁻¹ = ψ t * l * (ψ t)⁻¹

@[expose] def GGHalfSupportedAt {G : Type} [Group G] {N : ℕ} (X : Subgroup G)
    (ψ : SpecialLinearGroup (Fin (N + 1)) F2 →* G) (b : G) (P : Fin N) : Prop :=
  ∃ t ∈ Subgroup.zpowers (omegaBlock N P), GGHalfActsAs X ψ b t

@[expose] def GGHalfOrbit {G : Type} [Group G] {Bs : Subgroup G} (A : Subgroup (MulAut ↥Bs))
    (b : G) (hb : b ∈ Bs) : Set G :=
  {z : G | ∃ φ ∈ A, ((φ ⟨b, hb⟩ : ↥Bs) : G) = z}

end CFSG.StandardType

end
