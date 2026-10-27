module

public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.LieType.Ree.Duality

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

open CFSG.Blueprint.Chevalley (adjointGroup ModGL entrywiseHom TwistTag)

open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor)

open CFSG.LieType.Ree (ReeTag)

@[expose] def secondCenterSubgroup {K : Type} [Group K] (S : Subgroup K) : Subgroup K :=
  (_root_.upperCentralSeries ↥S 2).map S.subtype

@[expose] def Ok69 {K : Type} [Group K] (a : K) : Prop :=
  ∀ R : Subgroup K, IsPGroup 3 R → a ∈ normalizer (R : Set K) →
    (∀ z ∈ secondCenterSubgroup (R ⊔ zpowers a), a * z = z * a) ∧
      (a ∈ secondCenterSubgroup (R ⊔ zpowers a) →
        a ∈ (Subgroup.center ↥(R ⊔ zpowers a)).map (R ⊔ zpowers a).subtype)

@[expose] def OutOrderThree (Lb : Type) [Group Lb] (φ : MulAut Lb) : Prop :=
  ∀ α : MulAut Lb, α ∉ (MulAut.conj : Lb →* MulAut Lb).range →
    α ^ 3 ∈ (MulAut.conj : Lb →* MulAut Lb).range →
      ∃ g : Lb, α = MulAut.conj g * φ ∨ α = MulAut.conj g * φ ^ 2

@[expose] def OutTrialityInput :
    Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), p.Prime → p ≠ 3 → 1 ≤ f →
    Nat.card K = (p ^ f) ^ 3 → (∀ c, σ c = c ^ (p ^ f)) →
      OutOrderThree (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (fieldActor σ σ)

@[expose] def SD3 (H : Type*) [Group H] [Finite H] (Q T V : Subgroup H) (y : H)
    (e1 e2 : ℕ) : Prop :=
  IsPGroup 3 Q ∧ ¬ 3 ∣ Q.index ∧
  T ≤ Q ∧
  (T.subgroupOf Q).Normal ∧
  IsMulCommutative ↥T ∧
  V ≤ T ∧
  IsElemAbelian 3 V ∧
  (∀ t ∈ T, t ^ 3 = 1 → t ∈ V) ∧
  Q = T ⊔ Subgroup.zpowers y ∧
  (∀ v ∈ V, (y * v * y⁻¹ * v⁻¹) ∈ V ∧
    y * (y * v * y⁻¹ * v⁻¹) * y⁻¹ = y * v * y⁻¹ * v⁻¹) ∧
  (∃ v ∈ V, y * v * y⁻¹ ≠ v) ∧
  (∀ g ∈ Q, g ∉ T → ∃ v ∈ V, g * v * g⁻¹ ≠ v) ∧
  Nat.card V = 9 ∧
  orderOf y = 3 ∧
  Nonempty ((Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) ≃* ↥T)

@[expose] def ScalarAction {H : Type*} [Group H] (T : Subgroup H) (φ : MulAut H) (y : H)
    (k : ℤ) : Prop :=
  φ y = y ∧ ∀ t ∈ T, φ t = t ^ k

@[expose] def Fusion27 {H : Type*} [Group H] (z : H) : Prop :=
  ∃ R : Subgroup H, Nat.card R = 27 ∧ z ∈ R ∧
    z ∉ (Subgroup.center ↥R).map R.subtype

@[expose] def GOutTarget : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 3 → 3 ∣ f →
    Nat.card K = p ^ f →
    ∀ (eps : ℤ), (eps = 1 ∨ eps = -1) →
      ((p : ZMod 3) ^ (f / 3) = (eps : ZMod 3)) →
      ∀ σ₀ : K ≃+* K, (∀ c : K, σ₀ c = c ^ (p ^ (f / 3))) →
      ∀ φ : MulAut (adjointGroup .G2 K),
        (∀ h : adjointGroup .G2 K, (φ h : ModGL .G2 K) =
          Units.map (entrywiseHom σ₀.toRingHom) (h : ModGL .G2 K)) →
        ∃ (Q T V : Subgroup (adjointGroup .G2 K)) (y : adjointGroup .G2 K),
          SD3 (adjointGroup .G2 K) Q T V y
              (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)))
              (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) ∧
          ScalarAction T φ y (eps * (p : ℤ) ^ (f / 3))

@[expose] def G2SDTarget : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 3 → 1 ≤ f →
    Nat.card K = p ^ f → 3 ≤ p ^ f →
    ∀ (eps : ℤ), (eps = 1 ∨ eps = -1) →
      ((p : ZMod 3) ^ f = (eps : ZMod 3)) →
      ∃ (Q T V : Subgroup (adjointGroup .G2 K)) (y : adjointGroup .G2 K),
        SD3 (adjointGroup .G2 K) Q T V y
            (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)))
            (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) ∧
        Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3

@[expose] def TrialityTarget : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 3 → 1 ≤ f →
    Nat.card K = (p ^ f) ^ 3 →
    ∀ (σ : K ≃+* K), (∀ c : K, σ c = c ^ (p ^ f)) →
    ∀ (eps : ℤ), (eps = 1 ∨ eps = -1) →
      ((p : ZMod 3) ^ f = (eps : ZMod 3)) →
      ∃ (Q T V : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
        (y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        SD3 _ Q T V y
            (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)) + 1)
            (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) ∧
        ScalarAction T (fieldActor (t := TwistTag.D4) σ σ) y (eps * (p : ℤ) ^ f) ∧
        (∀ z ∈ V, z ≠ 1 → y * z * y⁻¹ = z → Fusion27 z)

@[expose] def OuterTorusDatum (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∃ (φ : MulAut Y) (Q T V : Subgroup Y) (y : Y) (e1 e2 : ℕ) (k : ℤ),
    φ ^ 3 = 1 ∧ OutOrderThree Y φ ∧ SD3 Y Q T V y e1 e2 ∧ ScalarAction T φ y k ∧
    (k : ZMod 3) = 1 ∧ ¬ ((3 : ℤ) ^ max e1 e2 ∣ k - 1)

@[expose] def OutCase (Y : Type) [Group Y] [Finite Y] : Prop :=
  ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ∨ OuterTorusDatum Y

@[expose] def NoOk69Order3 (Y : Type) [Group Y] : Prop :=
  ∀ a : Y, a ^ 3 = 1 → Ok69 a → a = 1

@[expose] def D4InnerDatum (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ S : Sylow 3 Y, ∃ (T V : Subgroup Y) (y : Y) (e1 e2 : ℕ),
    SD3 Y (S : Subgroup Y) T V y e1 e2 ∧ ∀ z ∈ V, z ≠ 1 → y * z * y⁻¹ = z → Fusion27 z

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
