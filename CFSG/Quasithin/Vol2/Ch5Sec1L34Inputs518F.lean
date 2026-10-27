module

public import CFSG.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def L34ParabolicFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .PSL 3 2 2 → ∀ S₀ : Subgroup X,
    IsSylowTwoOf S₀ ⊤ →
    ∃ P R : Subgroup X, Subgroup.normalizer (S₀ : Set X) ≤ P ∧ R ≤ S₀ ∧
      Subgroup.normalizer (R : Set X) = P ∧ IsElemAbelian 2 R ∧ Nat.card R = 16 ∧
      (∃ π : ↥P →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2),
        Function.Surjective π ∧ π.ker = R.subgroupOf P) ∧
      ∀ α : MulAut X, Odd (orderOf α) → S₀.map α.toMonoidHom = S₀ → R.map α.toMonoidHom = R

@[expose] def L34TwoAutFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .PSL 3 2 2 → ∀ S₀ : Subgroup X,
    IsSylowTwoOf S₀ ⊤ → ∀ α δ : MulAut X, (∃ m : ℕ, α ^ 2 ^ m = 1) →
      S₀.map α.toMonoidHom = S₀ → δ ^ 3 = 1 → δ ∉ (MulAut.conj : X →* MulAut X).range →
      (∃ m : ℕ, (α * δ * α⁻¹ * δ⁻¹) ^ 2 ^ m = 1) →
      ∀ b ∈ Subgroup.normalizer (S₀ : Set X), b ∉ S₀ → α b * b⁻¹ ∈ S₀ →
        ∃ x ∈ S₀, α = MulAut.conj x

@[expose] def F112L2FourChiefFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    F112ListALegacyBare L1 L2 S → ∀ Li : Subgroup G, (Li = L1 ∨ Li = L2) → IsL2Quot 2 (oTwoQuot ↥Li) →
      ∀ Z₀ : Subgroup G, Z₀ ≠ ⊥ → Z₀ ≤ centerOf S → Z₀ ≤ Subgroup.centralizer (Li : Set G) →
        ∀ n : ℕ, IsChiefSeriesFrom Li (pCoreOf 2 Li) (pCoreOf 2 Li) n → n ≤ 2

@[expose] def L34ParabolicChiefFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K U : Subgroup G), LieModel (O2Q K) .PSL 3 2 2 →
    CharTwo K → pCoreOf 2 K ≤ U → U ≤ K →
    (∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K) → (∀ x ∈ U, x ^ 2 ∈ pCoreOf 2 K) →
    Nat.card U = 16 * Nat.card (pCoreOf 2 K) →
      ∀ n : ℕ, IsChiefSeriesFrom (oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)))
        (pCoreOf 2 (oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G))))
        (pCoreOf 2 (oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)))) n → 3 ≤ n

end CFSG.Quasithin.H13
