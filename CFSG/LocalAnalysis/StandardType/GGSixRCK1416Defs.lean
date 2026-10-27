module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

@[expose] def FourAt {X : Type} [Group X] (J V : Subgroup X) (r : X) : Prop :=
  r ∈ V ∧ V ≤ J ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧ r ≠ 1 ∧
    ∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹

@[expose] def CoreCommAt {X : Type} [Group X] (J V : Subgroup X) (r : X) : Prop :=
  ∀ v ∈ V, ∀ y ∈ pCoreOf 2 (J ⊓ Subgroup.centralizer ({r} : Set X)),
    v * y * v⁻¹ * y⁻¹ ∈ Subgroup.zpowers r

@[expose] def WeakK1At {X : Type} [Group X] (J V : Subgroup X) (r : X) : Prop :=
  ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (J : Set X) →
    Y ≤ Subgroup.centralizer {r} →
    (∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y : Set X)) →
    ∀ v ∈ V, ∀ y ∈ Y, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set X),
      v * y * v⁻¹ * y⁻¹ = r ^ k * z

@[expose] def K2At {X : Type} [Group X] (K V : Subgroup X) (r : X) : Prop :=
  pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.normalizer (V : Set X)

@[expose] def Cent96At {X : Type} [Group X] (J : Subgroup X) (r : X) : Prop :=
  ∃ rJ : ↥J, (rJ : X) = r ∧ RCKPosCent 96 ↥J (QuotientGroup.mk' (Subgroup.center ↥J) rJ) ⊥

@[expose] def ShortAt
    {X : Type} [Group X] (J : Subgroup X) (r : X) : Prop :=
  ∃ rJ : ↥J, (rJ : X) = r ∧ RCKPosShort ↥J (QuotientGroup.mk' (Subgroup.center ↥J) rJ) ⊥

@[expose] def BlockOn {U F M : Type} [Group U] [Field F] [AddCommGroup M] [Module F M]
    (act : U → M → M) (W E : Submodule F M) (H : Subgroup U) : Prop :=
  IsCompl W E ∧ ∀ u : U, u ∈ H ↔ (∀ w ∈ W, act u w ∈ W) ∧ ∀ e ∈ E, act u e = e

@[expose] def SLFourEmbed {X : Type} [Group X] (K J : Subgroup X) : Prop :=
  ∃ (m : ℕ) (φ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1) →* X)
    (W E : Submodule (GaloisField 2 1) (Fin (m + 1) → GaloisField 2 1))
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1))),
    φ.range = K ∧ φ.ker ≤ Subgroup.center _ ∧
    BlockOn (fun (u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 1)) v =>
      (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 1)).mulVec v) W E H ∧
    H.map φ = J ∧ Module.finrank (GaloisField 2 1) W = 4

@[expose] def OmegaSixBlockVia {ι : Type}
    (Q : QuadraticForm (GaloisField 2 1) (ι → GaloisField 2 1)) {X : Type} [Group X]
    (K J : Subgroup X) : Prop :=
  ∃ (φ : spinGroup Q →* X) (W E : Submodule (GaloisField 2 1) (ι → GaloisField 2 1))
    (H : Subgroup (spinGroup Q)),
    φ.range = K ∧ φ.ker ≤ Subgroup.center (spinGroup Q) ∧
    BlockOn (fun u v => Spin.spinAction Q u v) W E H ∧ H.map φ = J ∧
    (∀ w ∈ W, ∀ e ∈ E, QuadraticMap.polar Q w e = 0) ∧
    Module.finrank (GaloisField 2 1) W = 6

@[expose] def OmegaSixEmbed {X : Type} [Group X] (K J : Subgroup X) : Prop :=
  (∃ n : ℕ, OmegaSixBlockVia (Spin.quadPlus n (GaloisField 2 1)) K J) ∨
  ∃ n : ℕ, OmegaSixBlockVia
    (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2) K J

@[expose] def OrthPointVia {ι : Type}
    (Q : QuadraticForm (GaloisField 2 1) (ι → GaloisField 2 1)) {X : Type} [Group X]
    (K V : Subgroup X) (r : X) : Prop :=
  ∃ (φ : spinGroup Q →* X) (r₀ : spinGroup Q) (V₀ : Subgroup (spinGroup Q))
    (z x : ι → GaloisField 2 1),
    φ.range = K ∧ φ.ker ≤ Subgroup.center (spinGroup Q) ∧ φ r₀ = r ∧ r₀ ∈ V₀ ∧ V₀.map φ = V ∧
    z ≠ 0 ∧ Q z = 0 ∧ QuadraticMap.polar Q z x = 0 ∧ Q x = 1 ∧
    Spin.spinAction Q r₀ = CFSG.ClassicalGroups.Orthogonal.eichler Q z x ∧
    V₀.map (Spin.spinAction Q) ≤ CFSG.ClassicalGroups.Orthogonal.rootGroup Q z

@[expose] def OrthPoint {X : Type} [Group X] (K V : Subgroup X) (r : X) : Prop :=
  (∃ n : ℕ, 3 ≤ n ∧ OrthPointVia (Spin.quadPlus n (GaloisField 2 1)) K V r) ∨
  ∃ n : ℕ, 3 ≤ n ∧ OrthPointVia
    (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2) K V r

end CFSG.StandardType.RCKC1
