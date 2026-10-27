module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Smith81.S81A5Beta
public import CFSG.RankThree.GF2n.Smith81.S81BA5Def
public import CFSG.RankThree.GF2n.Smith81.S81CCases

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube

@[expose] def Smith24E3LFormStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE3L M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∀ (ψ : M₀.E ≃ₗ[K] Cube K) (φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)),
            EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K) →
              ∃ lam : K, lam ≠ 0 ∧ ∀ e f : M₀.E, M₀.B e f = lam * beta K (ψ e) (ψ f)

end CFSG.RankThree.GF2n.Smith81
