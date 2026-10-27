module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogPieces
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2SwapMain

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique
open scoped commutatorElement

local instance e7CentNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def fs81CommSet {G : Type} [Group G] (Q : Subgroup G) (σ : G) : Set G :=
  {x | ∃ q ∈ Q, x = ⁅q, σ⁆}

@[expose] def fs81SigmaW {G : Type} [Group G] (Q : Subgroup G) (σ t₀ : G) : Subgroup G :=
  Subgroup.closure (fs81CommSet Q σ) ⊔ Subgroup.zpowers t₀

@[expose] def FS81HoltQuot : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (H Q L S : Subgroup X) (z : X),
    Q ≤ H → H ≤ Subgroup.normalizer (Q : Set X) → L ≤ H → L ⊓ Q = ⊥ →
    IsSimpleGroup ↥L → (∃ a c : ↥L, a * c ≠ c * a) →
    (∀ m : ℕ, 2 ≤ m → 2 * Nat.card ↥L ≠ (2 * m).factorial) →
    IsSylow2In S L → z ∈ S → orderOf z = 2 → (∀ s ∈ S, s * z = z * s) →
    (∀ h ∈ H, h * z * h⁻¹ ∈ L ⊔ Q → h ∈ L ⊔ Q) → H ≤ L ⊔ Q

@[expose] def FS81CentControl : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y H Q L M : Subgroup X) (σ b₀ : X),
    Q ≤ H → H ≤ Subgroup.normalizer (Q : Set X) → L ≤ H → L ⊓ Q = ⊥ → H ⊓ Y ≤ L ⊔ Q →
    σ ∈ L → orderOf σ = 2 → (∀ g : X, g * b₀ * g⁻¹ ∈ Y → g ∈ Y) → M ≤ Y →
    (∀ c ∈ H, ⁅c, σ⁆ ∈ Q → ∀ m ∈ M, c * m * c⁻¹ ∈ M) → (∃ y ∈ Y, y * b₀ * y⁻¹ ∈ M) →
    (∀ τ ∈ L, orderOf τ = 2 →
      ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ L ∧ τ * (y * b₀ * y⁻¹) = y * b₀ * y⁻¹ * τ) →
    ∀ h ∈ H, h * σ * h⁻¹ ∈ L ⊔ Q → h ∈ L ⊔ Q

@[expose] def FS81FlagTwoGroup : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (H Q C W Z N : Subgroup X),
    IsPGroup 2 Q → Z ≤ W → W ≤ C → C ≤ Q → N ≤ H →
    H ⊓ Subgroup.centralizer (Q : Set X) ≤ Q →
    (∀ n ∈ N, ∀ q ∈ Q, ⁅n, q⁆ ∈ C) → (∀ n ∈ N, ∀ c ∈ C, ⁅n, c⁆ ∈ W) →
    (∀ n ∈ N, ∀ w ∈ W, ⁅n, w⁆ ∈ Z) → (∀ n ∈ N, ∀ z ∈ Z, n * z = z * n) → IsPGroup 2 N

@[expose] def FS81SixLemma : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M P : Subgroup G) (b k b₁ : G),
    b ∈ M → k ∈ M → orderOf b = 3 → orderOf k = 2 → k * b * k⁻¹ = b⁻¹ →
    P ≤ Subgroup.normalizer (M : Set G) →
    Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    b₁ ∈ P → orderOf b₁ = 3 → (∀ p ∈ P, p * k = k * p) →
    (∀ m ∈ M, m * b = b * m → m ∈ Subgroup.zpowers b) →
    (∀ m ∈ M, m * b₁ = b₁ * m → m ∈ Subgroup.closure ({b, k} : Set G)) →
    M ≤ Subgroup.closure ({b, k} : Set G)

@[expose] def FS81SixLift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (C M N P : Subgroup G) (b k b₁ : G),
    N ≤ M → M ≤ C → C ≤ Subgroup.normalizer (N : Set G) → IsPGroup 2 N →
    P ≤ C → P ≤ Subgroup.normalizer (M : Set G) →
    b ∈ M → k ∈ M → orderOf b = 3 → orderOf k = 2 → k * b * k⁻¹ = b⁻¹ →
    Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    b₁ ∈ P → orderOf b₁ = 3 → (∀ p ∈ P, p * k = k * p) →
    (∀ m ∈ M, m * b = b * m → m ∈ N ⊔ Subgroup.zpowers b) →
    (∀ m ∈ M, m * b₁ = b₁ * m → m ∈ N ⊔ Subgroup.closure ({b, k} : Set G)) →
    M ≤ N ⊔ Subgroup.closure ({b, k} : Set G)

@[expose] def FS81CentM : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y H Q S K P : Subgroup X) (t₀ σ b k b₁ : X),
    Q ≤ H → H ≤ Subgroup.normalizer (Q : Set X) → IsPGroup 2 Q →
    H ⊓ Subgroup.centralizer (Q : Set X) ≤ Q →
    t₀ ∈ Q → (∀ h ∈ H, h * t₀ = t₀ * h) →
    (∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ⁅q₁, q₂⁆ ∈ Subgroup.zpowers t₀) → σ ∈ H →
    S ≤ H → IsPGroup 2 S → (∀ s ∈ S, s * σ = σ * s) →
    (∀ s ∈ S, ∀ w ∈ fs81CommSet Q σ, ⁅s, w⁆ ∈ Subgroup.zpowers t₀) →
    (∀ s ∈ S, ∀ q ∈ Q, ⁅⁅s, q⁆, σ⁆ ∈ Subgroup.zpowers t₀) →
    (∀ s ∈ S, ∀ c ∈ Q, ⁅c, σ⁆ ∈ Subgroup.zpowers t₀ → ⁅s, c⁆ ∈ fs81SigmaW Q σ t₀) →
    K ≤ H → K ≤ Subgroup.normalizer (S : Set X) → (∀ x ∈ K, x * σ = σ * x) →
    (∀ x ∈ K, ∀ w ∈ fs81CommSet Q σ, ⁅x, w⁆ ∈ Subgroup.zpowers t₀) →
    b ∈ K → k ∈ K → orderOf b = 3 → orderOf k = 2 → k * b * k⁻¹ = b⁻¹ →
    K ≤ Subgroup.closure ({b, k} : Set X) →
    P ≤ H → Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    (∀ p ∈ P, p * σ = σ * p) → (∀ p ∈ P, p * k = k * p) →
    P ≤ Subgroup.normalizer (S : Set X) → b₁ ∈ P → orderOf b₁ = 3 →
    Subgroup.centralizer ({b} : Set X) ≤ Y → Subgroup.centralizer ({b₁} : Set X) ≤ Y →
    (∀ h ∈ H ⊓ Y, ⁅h, σ⁆ ∈ Q →
      (∀ w ∈ fs81CommSet Q σ, ⁅h, w⁆ ∈ Subgroup.zpowers t₀) → h ∈ Q ⊔ S ⊔ K) →
    ∃ M : Subgroup X, K ≤ M ∧ M ≤ Q ⊔ S ⊔ K ∧
      ∀ c ∈ H, ⁅c, σ⁆ ∈ Q → ∀ m ∈ M, c * m * c⁻¹ ∈ M

abbrev e7Alpha7 : Fin (Tag.rank .E7) → ℤ := Pi.single 6 1

@[expose] noncomputable def e7A1 :
    Subgroup ↥(adjointGroup .E7 (ZMod 2)) :=
  (rootSubgroup .E7 (ZMod 2) e7Alpha7 ⊔ rootSubgroup .E7 (ZMod 2) (-e7Alpha7)).subgroupOf
    (adjointGroup .E7 (ZMod 2))

@[expose] noncomputable def e7D4 :
    Subgroup ↥(adjointGroup .E7 (ZMod 2)) :=
  overlapSpanD4 (ZMod 2) .high .seven

noncomputable abbrev e7CentSigma :
    ↥(adjointGroup .E7 (ZMod 2)) :=
  pinnedElt .E7 d6HighRoot (1 : ZMod 2)

noncomputable abbrev e7CentS :
    Subgroup ↥(adjointGroup .E7 (ZMod 2)) :=
  (rootSpan .E7 (ZMod 2) (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7)).subgroupOf
    (adjointGroup .E7 (ZMod 2))

noncomputable abbrev e7CentB :
    ↥(adjointGroup .E7 (ZMod 2)) :=
  pinnedElt .E7 e7Alpha7 (1 : ZMod 2) * pinnedElt .E7 (-e7Alpha7) (1 : ZMod 2)

noncomputable abbrev e7CentInvol :
    ↥(adjointGroup .E7 (ZMod 2)) :=
  pinnedElt .E7 e7Alpha7 (1 : ZMod 2)

@[expose] def E7CentModelSylow : Prop :=
  IsSimpleGroup ↥(perpLevi .E7 (ZMod 2)) ∧
    (∃ a c : ↥(perpLevi .E7 (ZMod 2)), a * c ≠ c * a) ∧
    (∀ m : ℕ, 2 ≤ m → 2 * Nat.card ↥(perpLevi .E7 (ZMod 2)) ≠ (2 * m).factorial) ∧
    e7CentSigma ∈ perpLevi .E7 (ZMod 2) ∧ orderOf e7CentSigma = 2 ∧
    ∃ U : Subgroup ↥(adjointGroup .E7 (ZMod 2)), IsSylow2In U (perpLevi .E7 (ZMod 2)) ∧
      e7CentSigma ∈ U ∧ ∀ u ∈ U, u * e7CentSigma = e7CentSigma * u

@[expose] def E7CentModelQ : Prop :=
  e7HighInv ∈ highRadical .E7 (ZMod 2) ∧
    (∀ q₁ ∈ highRadical .E7 (ZMod 2), ∀ q₂ ∈ highRadical .E7 (ZMod 2),
      ⁅q₁, q₂⁆ ∈ Subgroup.zpowers e7HighInv) ∧
    F4Pilot.IsTwoRadicalDecomp e7HighInv (highRadical .E7 (ZMod 2)) (perpLevi .E7 (ZMod 2))

@[expose] def E7CentModelFlag : Prop :=
  e7CentS ≤ perpLevi .E7 (ZMod 2) ∧ e7A1 ≤ perpLevi .E7 (ZMod 2) ∧ IsPGroup 2 e7CentS ∧
    (∀ s ∈ e7CentS, s * e7CentSigma = e7CentSigma * s) ∧
    (∀ x ∈ e7A1, x * e7CentSigma = e7CentSigma * x) ∧
    (∀ s ∈ e7CentS, ∀ w ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma,
      ⁅s, w⁆ ∈ Subgroup.zpowers e7HighInv) ∧
    (∀ x ∈ e7A1, ∀ w ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma,
      ⁅x, w⁆ ∈ Subgroup.zpowers e7HighInv) ∧
    (∀ s ∈ e7CentS, ∀ q ∈ highRadical .E7 (ZMod 2),
      ⁅⁅s, q⁆, e7CentSigma⁆ ∈ Subgroup.zpowers e7HighInv) ∧
    (∀ s ∈ e7CentS, ∀ c ∈ highRadical .E7 (ZMod 2),
      ⁅c, e7CentSigma⁆ ∈ Subgroup.zpowers e7HighInv →
        ⁅s, c⁆ ∈ fs81SigmaW (highRadical .E7 (ZMod 2)) e7CentSigma e7HighInv)

@[expose] def E7CentSRoots : Prop :=
  e7CentS = (rootSpan .E7 (ZMod 2) (radicalRoots .E7 d6HighRoot)).subgroupOf
      (adjointGroup .E7 (ZMod 2)) ⊓ perpLevi .E7 (ZMod 2)

@[expose] def E7CentModelJ : Prop :=
  e7D4 ≤ perpLevi .E7 (ZMod 2) ∧ (∀ j ∈ e7D4, j * e7CentSigma = e7CentSigma * j) ∧
    (∀ j ∈ e7D4, ∀ x ∈ e7A1, j * x = x * j) ∧
    e7A1 ≤ Subgroup.normalizer (e7CentS : Set ↥(adjointGroup .E7 (ZMod 2))) ∧
    e7D4 ≤ Subgroup.normalizer (e7CentS : Set ↥(adjointGroup .E7 (ZMod 2)))

@[expose] def E7CentModelM : Prop :=
  ∀ d ∈ perpLevi .E7 (ZMod 2), d * e7CentSigma = e7CentSigma * d →
    (∀ w ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma,
      ⁅d, w⁆ ∈ Subgroup.zpowers e7HighInv) →
    d ∈ e7CentS ⊔ e7A1

@[expose] def E7CentModelK : Prop :=
  e7CentB ∈ e7A1 ∧ e7CentInvol ∈ e7A1 ∧ orderOf e7CentB = 3 ∧ orderOf e7CentInvol = 2 ∧
    e7CentInvol * e7CentB * e7CentInvol⁻¹ = e7CentB⁻¹ ∧
    e7A1 ≤ Subgroup.closure ({e7CentB, e7CentInvol} : Set ↥(adjointGroup .E7 (ZMod 2))) ∧
    ∀ r ∈ e7JTheta, orderOf r = 3 →
      ∃ g : ↥(adjointGroup .E7 (ZMod 2)), g * r * g⁻¹ = e7CentB

@[expose] def E7CentModelP : Prop :=
  ∃ P : Subgroup ↥(adjointGroup .E7 (ZMod 2)), P ≤ e7D4 ∧
    Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    ∃ b₁ ∈ P, ∃ g : ↥(adjointGroup .E7 (ZMod 2)), g * e7CentB * g⁻¹ = b₁

@[expose] def E7CentModelInv : Prop :=
  ∀ τ ∈ perpLevi .E7 (ZMod 2), orderOf τ = 2 →
    ∃ g ∈ perpLevi .E7 (ZMod 2), τ * (g * e7CentB * g⁻¹) = g * e7CentB * g⁻¹ * τ

end CFSG.StandardType.FrameRoute.FS81
