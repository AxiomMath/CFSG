module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Smith81.S81BA5Def
public import CFSG.RankThree.GF2n.Smith81.S81CCases

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube

@[expose] def E3LRootEltStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE3L M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∀ (ψ : M₀.E ≃ₗ[K] Cube K) (φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)),
            EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K) →
              ∀ z ∈ Z, z ≠ 1 → ∀ t : G, IsConj z t → t ∈ M → t ∉ Q →
                ∃ s : Lgen M (LB M Q B), (s : G) * t⁻¹ ∈ Q ∧
                  ∃ g : GL (Fin 6) K, IsTransvec K g ∧ φ s = rhoEquiv K g

section Transport

variable {G : Type} [Group G] {M Q Z B : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

@[expose] def transport (ψ : M₀.E ≃ₗ[K] Cube K) (T : M₀.E ≃ₗ[K] M₀.E) : Cube K ≃ₗ[K] Cube K :=
  ψ.symm.trans (T.trans ψ)

theorem transport_apply (ψ : M₀.E ≃ₗ[K] Cube K) (T : M₀.E ≃ₗ[K] M₀.E) (e : M₀.E) :
    transport ψ T (ψ e) = ψ (T e) := by
  simp [transport]

theorem transport_mul (ψ : M₀.E ≃ₗ[K] Cube K) (T₁ T₂ : M₀.E ≃ₗ[K] M₀.E) :
    transport ψ (T₁ * T₂) = transport ψ T₁ * transport ψ T₂ := by
  ext ξ
  simp [transport]

theorem transport_one (ψ : M₀.E ≃ₗ[K] Cube K) : transport ψ 1 = 1 := by
  ext ξ
  simp [transport]

theorem transport_injective (ψ : M₀.E ≃ₗ[K] Cube K) :
    Function.Injective (transport ψ : (M₀.E ≃ₗ[K] M₀.E) → (Cube K ≃ₗ[K] Cube K)) := by
  intro T₁ T₂ h
  ext e
  have := congrArg (fun S : Cube K ≃ₗ[K] Cube K => S (ψ e)) h
  simp only [transport_apply] at this
  exact ψ.injective this

end Transport

end CFSG.RankThree.GF2n.Smith81
