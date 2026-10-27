module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorAlg
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Glue


structure IsTensorSetup {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (n : ℕ) {K : Type} [Field K] [Finite K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) : Prop where
  model : GlobalModelData M Q Z γ M₀
  card : Nat.card K = Nat.card Z
  dim : Module.finrank K M₀.E = 2 * n
  conj : ∀ (t : ↥M) (x : G), x ∈ Q →
    M₀.π ((t : G) * x * (t : G)⁻¹) = (ρ (QuotientGroup.mk t)).toAdd (M₀.π x)
  lin : ∀ g ∈ bar M Q (H0 M Z), ∀ (c : K) (v : M₀.E),
    (ρ g).toAdd (c • v) = c • (ρ g).toAdd v
  iso : ∀ g ∈ bar M Q (H0 M Z), ∀ v w : M₀.E,
    M₀.B ((ρ g).toAdd v) ((ρ g).toAdd w) = M₀.B v w
  b_ne : b ≠ 0
  fix : ∀ v : M₀.E, (∀ ℓ ∈ bar M Q (LB M Q B), (ρ ℓ).toAdd v = v) ↔
    v ∈ Submodule.span K {b}
  stab : ∀ g : Mbar M Q, (∃ c : K, (ρ g).toAdd b = c • b) →
    g ∈ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q))
  b_img : b ∈ M₀.img B

@[expose] def TensorSetupStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ)
      (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E), IsTensorSetup hc n M₀ ρ b

@[expose] def TensorSideStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ)
      (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E), IsTensorSetup hc n M₀ ρ b →
    ∀ (X : Subgroup (Mbar M Q)), IsQSNormalIn X (bar M Q (Lgen M (LB M Q B))) →
      ¬ IsSLModel 2 (Nat.card Z) ↥X → ∀ (t : ↥M), (t : G) ∈ LB M Q B →
      (QuotientGroup.mk t : Mbar M Q) ≠ 1 →
      (∀ x ∈ X, (QuotientGroup.mk t : Mbar M Q) * x = x * QuotientGroup.mk t) →
      ∃ (W : Submodule K M₀.E) (d : ℕ),
        TensorSide ρ b X (X ⊓ (bar M Q (LB M Q B) ⊔ bar M Q (hc.CN (t : G)))) W d


end Glue

end CFSG.RankThree.GF2n.Stroth80
