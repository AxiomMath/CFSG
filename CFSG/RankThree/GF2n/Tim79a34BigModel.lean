module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GF2n.Tim79a34BigEnd
public import CFSG.Timmesfeld.Transvection.ModelRadical

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

structure BigNatCfg (V H : Subgroup G) (hVH : V ≤ H) {n f : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)) : Prop where
  equiv : ∀ (x : ↥(xOf V H)) (v : Fin n ⊕ Fin n → GaloisField 2 f),
    ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 f) (Φ.symm (xToXbar hVH x)) *ᵥ v)) :
      ↥(wOf V H)) : G) = (x : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (x : G)⁻¹
  point : ∀ (a : Fin n ⊕ Fin n → GaloisField 2 f)
    (T : Subgroup ↥(StatedSp n (GaloisField 2 f))), a ≠ 0 → CaseM.IsTransGroup a T →
    T.map Φ.toMonoidHom = Vy V H → ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ∈ V

@[expose] def SpRadGeneralStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (F : Type) [Field F] [CharP F 2] [Finite F],
    ∀ (a : Fin n ⊕ Fin n → F), a ≠ 0 →
      (∀ g ∈ spRad a, ∀ h ∈ spRad a, g * h = h * g) ∧ (∀ g ∈ spRad a, g * g = 1) ∧
        Nat.card ↥(spRad a) = Nat.card F ^ (2 * n - 1)

@[expose] def BigPLocalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : BigEndHyp M V Q P H),
    Subgroup.center (Xbar V H) = ⊥ → cPbar V H P ≤ wOf V H →
    ∀ {n f : ℕ}, 2 ^ f = qBar V H →
    ∀ (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H)
      (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)),
      BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ →
      ∀ (a : Fin n ⊕ Fin n → GaloisField 2 f)
        (T : Subgroup ↥(StatedSp n (GaloisField 2 f))), a ≠ 0 → CaseM.IsTransGroup a T →
        T.map Φ.toMonoidHom = Vy V H →
        (∀ w, ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P ↔ CaseM.spForm a w = 0) ∧
        Rbar V H P = (spRad a).map Φ.toMonoidHom ∧ xOf V H = H ∧
        Nat.card ↥P = qBar V H ^ (4 * n - 2)

@[expose] def BigPCommutatorStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : BigEndHyp M V Q P H),
    Subgroup.center (Xbar V H) = ⊥ → cPbar V H P ≤ wOf V H →
    ⁅P, P⁆ = V ⊓ wOf V H ∧ inSubgroup frattini P = V ⊓ wOf V H ∧
      Subgroup.centralizer (P : Set G) = V

@[expose] def BigPCoverStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : BigEndHyp M V Q P H),
    Subgroup.center (Xbar V H) = ⊥ → cPbar V H P ≤ wOf V H →
    ∀ {n f : ℕ}, 2 ^ f = qBar V H →
    ∀ (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H)
      (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)),
      BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ →
      ∀ (a : Fin n ⊕ Fin n → GaloisField 2 f)
        (T : Subgroup ↥(StatedSp n (GaloisField 2 f))), a ≠ 0 → CaseM.IsTransGroup a T →
        T.map Φ.toMonoidHom = Vy V H →
        ∀ (b : Fin n ⊕ Fin n → GaloisField 2 f), CaseM.spForm a b ≠ 0 →
          ∀ w ∈ P ⊓ wOf V H, ∃ p ∈ P, ⁅p, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ = w

@[expose] def BigRootElementStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : BigEndHyp M V Q P H),
    Subgroup.center (Xbar V H) = ⊥ → cPbar V H P ≤ wOf V H →
    ∀ {n f : ℕ}, 2 ^ f = qBar V H →
    ∀ (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H)
      (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)),
      BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ →
      ∀ (a : Fin n ⊕ Fin n → GaloisField 2 f)
        (T : Subgroup ↥(StatedSp n (GaloisField 2 f))), a ≠ 0 → CaseM.IsTransGroup a T →
        T.map Φ.toMonoidHom = Vy V H →
        ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f),
          CaseM.spForm a c = 0 → (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
          ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
            ∀ y, r * ((Additive.toMul (ψ y) : ↥(wOf V H)) : G) * r⁻¹ =
              ((Additive.toMul (ψ (y + (μ * CaseM.spForm c y) • c)) : ↥(wOf V H)) : G)

end CFSG.RankThree.GF2n.Tim79a
