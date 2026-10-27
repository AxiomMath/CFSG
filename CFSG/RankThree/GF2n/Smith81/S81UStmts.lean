module

public import CFSG.RankThree.GF2n.Smith81.S81UModelData

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

@[expose] def E3URootEltStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE3U M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ) (_ : Nat.card F = (2 ^ f) ^ 2)
            (e : K ≃+* Fσ (unitaryInvolution F 2 f))
            (ψ : M₀.E ≃ₗ[K] E3UWspace (unitaryInvolution F 2 f) e)
            (φ : Lgen M (LB M Q B) →*
              (E3UWspace (unitaryInvolution F 2 f) e ≃ₗ[K] E3UWspace (unitaryInvolution F 2 f) e)),
            EUniData M Q Z B M₀ ψ φ (e3uGam (unitaryInvolution F 2 f) e)
              (e3uP0 (unitaryInvolution F 2 f) e) (e3uU0 (unitaryInvolution F 2 f) e) →
              ∀ z ∈ Z, z ≠ 1 → ∀ t : G, IsConj z t → t ∈ M → t ∉ Q →
                ∃ s : Lgen M (LB M Q B), (s : G) * t⁻¹ ∈ Q ∧
                  ∃ g : SUid (unitaryInvolution F 2 f) 6, IsTransvec F (g : GL (Fin 6) F) ∧
                    φ s = e3uWact (unitaryInvolution F 2 f) e g

end CFSG.RankThree.GF2n.Smith81
