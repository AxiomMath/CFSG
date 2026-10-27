module

public import CFSG.RankThree.GF2n.Tim79a34Local
public import CFSG.RankThree.GF2n.Stroth78.Reduction
public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa IsExtraspecial2 HasWidth)
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure QPCfg (M V Q P H : Subgroup G) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1))) :
    Prop where
  hyp : TwoEndHyp M V Q P H
  centre : Subgroup.center (Xbar V H) = ⊥
  iw : cPbar V H P ≤ wOf V H
  qp : Q ≤ P
  three : 3 ≤ n
  nat : NatCfg V H hyp.setup.mc.toMinCex.V_le_H Φ ψ
  ne : a ≠ 0
  trans : CaseM.IsTransGroup a T
  point : T.map Φ.toMonoidHom = Vy V H

@[expose] def QPCfg.aG {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (_ : QPCfg M V Q P H Φ ψ a T) : G := ((Additive.toMul (ψ a) : ↥(wOf V H)) : G)

@[expose] def NTStrothHypStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1)))
    (cfg : QPCfg M V Q P H Φ ψ a T),
    ∃ (E F : Subgroup G) (w : ℕ), StrothHyp cfg.aG E F ∧ w = 2 * n - 2 ∧
      Nat.card F = 2 ^ (2 * w + 1)

@[expose] def NTStrothSimpleStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1)))
    (cfg : QPCfg M V Q P H Φ ψ a T) (w : ℕ), w = 2 * n - 2 →
    ¬ StrothCaseI cfg.aG ∧ ¬ StrothCaseII cfg.aG w ∧ ¬ StrothCaseIII cfg.aG w ∧
      ¬ StrothCaseIV cfg.aG w ∧ ¬ StrothCaseVI cfg.aG w ∧ ¬ StrothCaseVII cfg.aG w

@[expose] def NTCaseVStatement : Prop :=
  ParrottFi22Statement → OMinusSixTwoAutPSp43Statement → Fi22InvolutionCentralizerStatement →
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1)))
    (cfg : QPCfg M V Q P H Φ ψ a T) (w : ℕ), w = 2 * n - 2 → ¬ StrothCaseV cfg.aG w

@[expose] def NTCaseVIIIStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1)))
    (cfg : QPCfg M V Q P H Φ ψ a T) (w : ℕ), w = 2 * n - 2 → ¬ StrothCaseVIII cfg.aG w

@[expose] def QPCfgExistsStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (hH : TwoEndHyp M V Q P H),
    Subgroup.center (Xbar V H) = ⊥ →
    (∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) → Q ≤ P →
    ∃ (n : ℕ) (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
      (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
      (a : Fin n ⊕ Fin n → GaloisField 2 1)
      (T : Subgroup ↥(StatedSp n (GaloisField 2 1))), Nonempty (QPCfg M V Q P H Φ ψ a T)

@[expose] def QPCfgSec4SetupStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1)))
    (cfg : QPCfg M V Q P H Φ ψ a T),
    Stroth78.Stroth78Assumption212 cfg.aG ∧
      ∃ b : G, b ∈ Stroth78.Q cfg.aG ∧ b ∉ Stroth78.ZQ cfg.aG ∧ IsConj cfg.aG b ∧
        cfg.aG ∈ Stroth78.QaOf b

end CFSG.RankThree.GF2n.Tim79a
