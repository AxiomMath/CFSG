module

public import CFSG.RankThree.GF2n.Tim79a34TwoEnd
public import CFSG.Timmesfeld.ARS.CaseMSp
public import CFSG.Timmesfeld.Transvection.ModelRankBasic

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def CXWStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), TwoEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ →
    ∀ x ∈ xOf V H, (∀ w ∈ wOf V H, x * w = w * x) → x ∈ wOf V H

@[expose] def MemberUniqueStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), TwoEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ →
    ∀ U ∈ omegaOf V H, ∀ U' ∈ omegaOf V H, U' ≤ U ⊔ wOf V H → U' = U

@[expose] def NaturalModuleStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : TwoEndHyp M V Q P H),
    Subgroup.center (Xbar V H) = ⊥ →
    ∃ (n : ℕ) (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
      (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)), 2 ≤ n ∧
      (∀ (x : ↥(xOf V H)) (v : Fin n ⊕ Fin n → GaloisField 2 1),
        ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 1)
          (Φ.symm (xToXbar hH.setup.mc.toMinCex.V_le_H x)) *ᵥ v)) : ↥(wOf V H)) : G) =
          (x : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (x : G)⁻¹) ∧
      (∃ (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1))),
        a ≠ 0 ∧ CaseM.IsTransGroup a T ∧ T.map Φ.toMonoidHom = Vy V H) ∧
      (∀ (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1))),
        a ≠ 0 → CaseM.IsTransGroup a T → T.map Φ.toMonoidHom = Vy V H →
        ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ∈ V)

end CFSG.RankThree.GF2n.Tim79a
