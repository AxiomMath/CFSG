module

public import CFSG.RankThree.GF2n.Tim79a34TwoEnd
public import CFSG.Timmesfeld.Transvection.ModelRadical

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

structure NatCfg (V H : Subgroup G) (hVH : V ≤ H) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)) : Prop where
  equiv : ∀ (x : ↥(xOf V H)) (v : Fin n ⊕ Fin n → GaloisField 2 1),
    ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 1) (Φ.symm (xToXbar hVH x)) *ᵥ v)) :
      ↥(wOf V H)) : G) = (x : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (x : G)⁻¹
  point : ∀ (a : Fin n ⊕ Fin n → GaloisField 2 1)
    (T : Subgroup ↥(StatedSp n (GaloisField 2 1))), a ≠ 0 → CaseM.IsTransGroup a T →
    T.map Φ.toMonoidHom = Vy V H → ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ∈ V

@[expose] def Lemma11aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : TwoEndHyp M V Q P H),
    Subgroup.center (Xbar V H) = ⊥ → cPbar V H P ≤ wOf V H →
    ∀ {n : ℕ} (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
      (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)),
      NatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ →
      ∀ (a : Fin n ⊕ Fin n → GaloisField 2 1)
        (T : Subgroup ↥(StatedSp n (GaloisField 2 1))), a ≠ 0 → CaseM.IsTransGroup a T →
        T.map Φ.toMonoidHom = Vy V H →
        (∀ w, ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P ↔ CaseM.spForm a w = 0) ∧
        Rbar V H P = (spRad a).map Φ.toMonoidHom ∧ xOf V H = H ∧
        Nat.card ↥P = 2 ^ (4 * n - 2)

@[expose] def Lemma11bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : TwoEndHyp M V Q P H),
    Subgroup.center (Xbar V H) = ⊥ → cPbar V H P ≤ wOf V H →
    ⁅P, P⁆ = V ⊓ wOf V H ∧ inSubgroup frattini P = V ⊓ wOf V H ∧
      Subgroup.centralizer (P : Set G) = V

@[expose] def Lemma11cStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : TwoEndHyp M V Q P H),
    Subgroup.center (Xbar V H) = ⊥ → cPbar V H P ≤ wOf V H →
    ∀ {n : ℕ} (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
      (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)),
      NatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ →
      ∀ (a : Fin n ⊕ Fin n → GaloisField 2 1)
        (T : Subgroup ↥(StatedSp n (GaloisField 2 1))), a ≠ 0 → CaseM.IsTransGroup a T →
        T.map Φ.toMonoidHom = Vy V H →
        ∀ (b : Fin n ⊕ Fin n → GaloisField 2 1), CaseM.spForm a b = 1 →
          (∀ v ∈ V, v ∉ wOf V H → ⁅v, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ =
            ((Additive.toMul (ψ a) : ↥(wOf V H)) : G)) ∧
          (∀ w ∈ P ⊓ wOf V H, ∃ p ∈ P, ⁅p, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ = w)

@[expose] def Lemma12Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : TwoEndHyp M V Q P H),
    Subgroup.center (Xbar V H) = ⊥ →
    ∀ {n : ℕ} (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
      (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)),
      NatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ →
      ∀ (a : Fin n ⊕ Fin n → GaloisField 2 1)
        (T : Subgroup ↥(StatedSp n (GaloisField 2 1))), a ≠ 0 → CaseM.IsTransGroup a T →
        T.map Φ.toMonoidHom = Vy V H →
        Subgroup.centralizer ({((Additive.toMul (ψ a) : ↥(wOf V H)) : G)} : Set G) = M ∧
        xOf V H ⊓ Subgroup.centralizer ({((Additive.toMul (ψ a) : ↥(wOf V H)) : G)} : Set G) ≤ M ∧
        Q ⊓ xOf V H = P ∧ wOf V H ⊓ Q = P ⊓ wOf V H ∧
        ¬ M ≤ Subgroup.normalizer (wOf V H : Set G)

@[expose] def Lemma13Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), TwoEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ → cPbar V H P ≤ wOf V H →
    ∀ v ∈ V, v ∉ wOf V H →
      Subgroup.centralizer ({v} : Set G) = M ⊓ Subgroup.centralizer (V : Set G) ∧
      Nat.card ↥M = 2 * Nat.card ↥(M ⊓ Subgroup.centralizer (V : Set G))

end CFSG.RankThree.GF2n.Tim79a
