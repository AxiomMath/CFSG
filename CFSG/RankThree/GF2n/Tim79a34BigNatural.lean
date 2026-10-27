module

public import CFSG.RankThree.GF2n.Tim79a34BigEnd
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Timmesfeld.ARS.CaseMSp
public import CFSG.Timmesfeld.Transvection.ModelRankBasic

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def BigNaturalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : BigEndHyp M V Q P H),
    Subgroup.center (Xbar V H) = ⊥ →
    ∃ (n f : ℕ) (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H)
      (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)), 2 ≤ n ∧
      2 ^ f = qBar V H ∧
      (∀ (x : ↥(xOf V H)) (v : Fin n ⊕ Fin n → GaloisField 2 f),
        ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 f)
          (Φ.symm (xToXbar hH.setup.mc.toMinCex.V_le_H x)) *ᵥ v)) : ↥(wOf V H)) : G) =
          (x : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (x : G)⁻¹) ∧
      (∃ (a : Fin n ⊕ Fin n → GaloisField 2 f) (T : Subgroup ↥(StatedSp n (GaloisField 2 f))),
        a ≠ 0 ∧ CaseM.IsTransGroup a T ∧ T.map Φ.toMonoidHom = Vy V H) ∧
      (∀ (a : Fin n ⊕ Fin n → GaloisField 2 f) (T : Subgroup ↥(StatedSp n (GaloisField 2 f))),
        a ≠ 0 → CaseM.IsTransGroup a T → T.map Φ.toMonoidHom = Vy V H →
        ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ∈ V)

@[expose] def BigIWStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ → cPbar V H P ≤ wOf V H

@[expose] def BigGammaStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ →
    ∃ C : Subgroup G, C ≤ Q ∧ P ⊔ C = Q ∧ (∀ p ∈ P, ∀ c ∈ C, ⁅p, c⁆ ∈ V ⊓ wOf V H) ∧
      (∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c) ∧ (∀ c ∈ C, ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H) ∧
      P.relIndex Q ≤ qBar V H ∧ Assembly.IsElemAbelian 2 C

@[expose] def BigQWStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    Q ⊓ wOf V H = P ⊓ wOf V H

end CFSG.RankThree.GF2n.Tim79a
