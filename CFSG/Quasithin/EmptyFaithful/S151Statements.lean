module

public import CFSG.Quasithin.EmptyFaithful.S141
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Quasithin.Vol2.Ch3Sec1Defs
public import CFSG.Quasithin.Background.D2Decomp

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] noncomputable def preOn (M V : Subgroup G) (L : Subgroup (MulAut V)) : Subgroup G :=
  M ⊓ (L.comap (conjAct V)).map (Subgroup.normalizer (V : Set G)).subtype

section Finite

variable [Finite G]

open Classical in
@[expose] noncomputable def qhatOn (M V : Subgroup G) : WithTop ℚ :=
  if hV : IsElemAbelian 2 V then
    @qhatOf ↥V (commGroupOfElemAbelian hV) inferInstance (autOn M V) else ⊤

open Classical in
@[expose] noncomputable def qOn (M V : Subgroup G) : WithTop ℚ :=
  if hV : IsElemAbelian 2 V then qInt M V hV else ⊤

open Classical in
@[expose] noncomputable def QhatStarOn (M V : Subgroup G) : Set (Subgroup (MulAut V)) :=
  if hV : IsElemAbelian 2 V then
    @QhatStar ↥V (commGroupOfElemAbelian hV) inferInstance (autOn M V) else ∅

open Classical in
@[expose] noncomputable def JhatOn (M V : Subgroup G) : Subgroup (MulAut V) :=
  if hV : IsElemAbelian 2 V then
    @Jhat ↥V (commGroupOfElemAbelian hV) inferInstance (autOn M V) else ⊥

@[expose] def IsOmegaFourPlusOn (M V : Subgroup G) : Prop :=
  ∃ hV : IsElemAbelian 2 V,
    @IsOmegaFourPlus ↥V (commGroupOfElemAbelian hV) (autOn M V)

@[expose] noncomputable def mJ154 (T M : Subgroup G) : Subgroup G :=
  preOn M (VZ T M) (JhatOn M (VZ T M))

@[expose] noncomputable def uJ154 (T M : Subgroup G) : Subgroup G := ⁅VZ T M, mJ154 T M⁆

@[expose] noncomputable def cJ154 (T M : Subgroup G) : Subgroup G :=
  VZ T M ⊓ Subgroup.centralizer (mJ154 T M : Set G)

@[expose] def Case1512Six (T Mc M : Subgroup G) : Prop :=
  Nonempty (↥(JhatOn M (VZ T M)) ≃* DihedralGroup 3) ∧
  uJ154 T M ⊓ cJ154 T M = ⊥ ∧ uJ154 T M ⊔ cJ154 T M = VZ T M ∧
  Nat.card (uJ154 T M) = 16 ∧ cJ154 T M ≠ ⊥ ∧
  IsOmegaFourPlusOn M (uJ154 T M) ∧
  ((M ⊓ Subgroup.centralizer (uJ154 T M : Set G) : Subgroup G) : Set G) *
      ((M ⊓ Subgroup.centralizer (cJ154 T M : Set G) : Subgroup G) : Set G) * (T : Set G) =
    ((M ⊓ Mc : Subgroup G) : Set G) ∧
  (M ⊓ Mc).relIndex M = 3

open Classical in
@[expose] noncomputable def V154 (T Mc M : Subgroup G) : Subgroup G :=
  if Case1512Six T Mc M then uJ154 T M else VZ T M

@[expose] noncomputable def mBar0 (T Mc M : Subgroup G) : Subgroup (MulAut (V154 T Mc M)) :=
  JhatOn M (V154 T Mc M)

@[expose] noncomputable def m0Of (T Mc M : Subgroup G) : Subgroup G :=
  preOn M (V154 T Mc M) (mBar0 T Mc M)

@[expose] def IsCE1513 (T M : Subgroup G) : Prop :=
  Nat.card (VZ T M) ≠ 4 ∧ ¬ IsOFourPlusAction M (VZ T M)

@[expose] def fittingIn {A : Type*} [Group A] (X : Subgroup A) : Subgroup A :=
  (CFSG.fittingSubgroup ↥X).map X.subtype

@[expose] def ElementaryNineShape (M V : Subgroup G) (A₀ : Subgroup (MulAut V)) : Prop :=
  IsElemAbelian 3 (oTwoUpper (autOn M V)) ∧ Nat.card (oTwoUpper (autOn M V)) = 9 ∧
    ∃ t : MulAut V, orderOf t = 2 ∧ (∀ x ∈ oTwoUpper (autOn M V), t * x * t⁻¹ = x⁻¹) ∧
      A₀ = oTwoUpper (autOn M V) ⊔ Subgroup.zpowers t

@[expose] def ExtraspecialThreeShape (T M V : Subgroup G) (A₀ : Subgroup (MulAut V)) : Prop :=
  IsPOnePlusTwo 3 ↥(oTwoUpper (autOn M V)) ∧
    (∃ t : MulAut V, orderOf t = 2 ∧
      (∀ x ∈ oTwoUpper (autOn M V), t * x * t⁻¹ * x ∈ frattiniIn (oTwoUpper (autOn M V))) ∧
      A₀ = oTwoUpper (autOn M V) ⊔ Subgroup.zpowers t) ∧
    IsIrredOnSection (autOn T V) (oTwoUpper (autOn M V)) (frattiniIn (oTwoUpper (autOn M V)))

@[expose] def IsDihedralParam (p m : ℕ) : Prop :=
  (p = 3 ∧ m = 1) ∨ (p = 3 ∧ m = 2) ∨ (p = 5 ∧ m = 2)

@[expose] def IsDirectSumOfCommutators (M V : Subgroup G) (A₁ A₂ : Subgroup (MulAut V)) : Prop :=
  ⁅V, preOn M V A₁⁆ ⊓ ⁅V, preOn M V A₂⁆ = ⊥ ∧ ⁅V, preOn M V A₁⁆ ⊔ ⁅V, preOn M V A₂⁆ = V

@[expose] def IsInternalDirect {X : Type*} [Group X] (A A₁ A₂ : Subgroup X) : Prop :=
  A = A₁ ⊔ A₂ ∧ A₁ ⊓ A₂ = ⊥ ∧ ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a

@[expose] def Case1512One (V : Subgroup G) (AJ : Subgroup (MulAut V)) : Prop :=
  ∃ p m : ℕ, IsDihedralParam p m ∧ Nonempty (↥AJ ≃* DihedralGroup p) ∧
    Nat.card V = 2 ^ (2 * m)

@[expose] def Case1512Two (M V : Subgroup G) (AJ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ autOn M V = AJ ∧ IsOmegaFourPlusOn M V ∧
    Nonempty (↥AJ ≃* DihedralGroup 3 × DihedralGroup 3)

@[expose] def Case1512Three (M V : Subgroup G) (AJ : Subgroup (MulAut V)) : Prop :=
  ∃ (p m : ℕ) (A₁ A₂ : Subgroup (MulAut V)), IsDihedralParam p m ∧ IsInternalDirect AJ A₁ A₂ ∧
    Nonempty (↥A₁ ≃* DihedralGroup p) ∧ Nonempty (↥A₂ ≃* DihedralGroup p) ∧
    IsDirectSumOfCommutators M V A₁ A₂ ∧
    Nat.card (⁅V, preOn M V A₁⁆ : Subgroup G) = 2 ^ (2 * m) ∧
    Nat.card (⁅V, preOn M V A₂⁆ : Subgroup G) = 2 ^ (2 * m) ∧
    ∃ x ∈ autOn M V, A₁.map (MulAut.conj x).toMonoidHom = A₂ ∧
      A₂.map (MulAut.conj x).toMonoidHom = A₁

@[expose] def Case1512Four (T M V : Subgroup G) (AJ : Subgroup (MulAut V)) : Prop :=
  ExtraspecialThreeShape T M V AJ ∧ Nat.card V = 64

@[expose] def Case1512Five (T M V : Subgroup G) (AJ : Subgroup (MulAut V)) : Prop :=
  ElementaryNineShape M V AJ ∧ Nat.card V = 16 ∧
    Nonempty (↥(autOn T V) ≃* Multiplicative (ZMod 4))

@[expose] def Lemma1512Concl (T Mc M : Subgroup G) : Prop :=
  Case1512One (VZ T M) (JhatOn M (VZ T M)) ∨ Case1512Two M (VZ T M) (JhatOn M (VZ T M)) ∨
    Case1512Three M (VZ T M) (JhatOn M (VZ T M)) ∨
    Case1512Four T M (VZ T M) (JhatOn M (VZ T M)) ∨
    Case1512Five T M (VZ T M) (JhatOn M (VZ T M)) ∨ Case1512Six T Mc M

@[expose] def Case1517One (M V : Subgroup G) (A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ autOn M V = A₀ ∧ Nonempty (↥A₀ ≃* DihedralGroup 3)

@[expose] def Case1517Two (M V : Subgroup G) (A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ Nonempty (↥A₀ ≃* DihedralGroup 3) ∧
    Nonempty (↥(autOn M V) ≃* DihedralGroup 3 × Multiplicative (ZMod 3))

@[expose] def Case1517Three (M V : Subgroup G) (A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ autOn M V = A₀ ∧ IsOmegaFourPlusOn M V

@[expose] def Case1517Four (T M V : Subgroup G) (A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ ElementaryNineShape M V A₀ ∧ Nonempty (↥(autOn T V) ≃* Multiplicative (ZMod 4))

@[expose] def Case1517Five (T M V : Subgroup G) (A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ Nonempty (↥A₀ ≃* DihedralGroup 5) ∧
    (Nonempty (↥(autOn T V) ≃* Multiplicative (ZMod 2)) ∨
      Nonempty (↥(autOn T V) ≃* Multiplicative (ZMod 4))) ∧
    (fittingIn (autOn M V) = fittingIn A₀ ∨
      Nonempty (↥(fittingIn (autOn M V)) ≃* Multiplicative (ZMod 15)))

@[expose] def Case1517Six (T M V : Subgroup G) (A₀ : Subgroup (MulAut V)) (p : ℕ) : Prop :=
  Nat.card V = 256 ∧ ∃ A₁ A₂ : Subgroup (MulAut V), IsInternalDirect A₀ A₁ A₂ ∧
    Nonempty (↥A₁ ≃* DihedralGroup p) ∧ Nonempty (↥A₂ ≃* DihedralGroup p) ∧
    (∃ t ∈ T, (preOn M V A₁).map (MulAut.conj t).toMonoidHom = preOn M V A₂) ∧
    IsDirectSumOfCommutators M V A₁ A₂

@[expose] def Case1517Seven (T M V : Subgroup G) (A₀ : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 64 ∧ ExtraspecialThreeShape T M V A₀

@[expose] def Lemma1517Cases (T M V : Subgroup G) (A₀ : Subgroup (MulAut V)) : Prop :=
  Case1517One M V A₀ ∨ Case1517Two M V A₀ ∨ Case1517Three M V A₀ ∨ Case1517Four T M V A₀ ∨
    Case1517Five T M V A₀ ∨ (∃ p : ℕ, (p = 3 ∨ p = 5) ∧ Case1517Six T M V A₀ p) ∨
    Case1517Seven T M V A₀

@[expose] def Lemma1517Concl (T Mc M : Subgroup G) : Prop :=
  Lemma1517Cases T M (V154 T Mc M) (mBar0 T Mc M) ∧
    (V154 T Mc M < VZ T M → Case1517Three M (V154 T Mc M) (mBar0 T Mc M))

@[expose] def StageLemma1517 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma1517Concl T Mc M

@[expose] def IsDualFFOn (M₀ V : Subgroup G) : Prop :=
  ∃ hV : IsElemAbelian 2 V, IsDualFFInt M₀ V hV

@[expose] def Theorem316Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315 T M M₀ H V,
      (∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
          M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)) ∨
      (¬ V ≤ pCoreOf 2 H ∧ qhatInt M₀ V h.reduced.2.2.1 ≤ 2 ∧
        (IsTISetIn V M → qhatInt M₀ V h.reduced.2.2.1 < 2)) ∨
      qInt M₀ V h.reduced.2.2.1 ≤ 2

@[expose] def Theorem317Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → Hyp315 T M M₀ H V → thompsonJ T ≤ pCoreOf 2 M₀ →
      (quasithinOmegaOneCenter T ≤ centerOf H ∧ centerOf M₀ = ⊥) ∨
      ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧ M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)

@[expose] def StageLemma1511 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M →
    (∀ H : Subgroup G, IsHStar T M H →
      Hyp315Base T M (M ⊓ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G)) H (VZ T M) ∧
      Hyp315.CaseII M H (VZ T M)) ∧
    (qhatOn M (VZ T M) ≤ 2 ∧ (2 < qOn M (VZ T M) → qhatOn M (VZ T M) < 2))

structure Lemma1515Concl (T Mc M : Subgroup G) : Prop where
  gen : V154 T Mc M = conjClosure (quasithinOmegaOneCenter T ⊓ V154 T Mc M) (m0Of T Mc M)
  reduced : IsTwoReducedIn M (V154 T Mc M)
  centralizer_le : Subgroup.centralizer (V154 T Mc M : Set G) ≤ Mc

@[expose] def StageLemma1515 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → Lemma1515Concl T Mc M

@[expose] def Description1512 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M →
    V154 T Mc M = conjClosure (quasithinOmegaOneCenter T ⊓ V154 T Mc M) (m0Of T Mc M)

@[expose] def IsTwoNilpotentOn (M V : Subgroup G) : Prop :=
  ∃ N : Subgroup (MulAut V), N ≤ autOn M V ∧ (∀ g ∈ autOn M V, ∀ y ∈ N, g * y * g⁻¹ ∈ N) ∧
    Odd (Nat.card N) ∧ ∀ x ∈ autOn M V, ∃ k : ℕ, x ^ 2 ^ k ∈ N

@[expose] def Nilpotency1512 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsTwoNilpotentOn M (V154 T Mc M)

@[expose] def StageLemma1516 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M →
    oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer (V154 T Mc M : Set G)

@[expose] def Lemma1518Concl (T Mc M : Subgroup G) : Prop :=
  (qhatOn M (V154 T Mc M) = 2 ∧ qOn M (V154 T Mc M) = 2) ∨
    (Case1517Three M (V154 T Mc M) (mBar0 T Mc M) ∧
      qhatOn M (V154 T Mc M) = ((3 / 2 : ℚ) : WithTop ℚ) ∧ qOn M (V154 T Mc M) = 2)

@[expose] def StageLemma1518 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma1518Concl T Mc M

structure Lemma1519Concl (T Mc M : Subgroup G) : Prop where
  one_commute : ⁅V154 T Mc M, thompsonJ T⁆ = ⊥
  one_commute_VZ : ⁅VZ T M, thompsonJ T⁆ = ⊥
  one_baum : baum T = baum (T ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
  one_cgs : CGS (baum T) ≤ M
  two : IsGreatestOrd T M
  three : ∀ H : Subgroup G, IsHStar T M H →
    H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Mc
  four : ∀ H : Subgroup G, IsHStar T M H →
    oTwoUpper (H ⊓ M) ≤ Subgroup.centralizer (V154 T Mc M : Set G)
  five : IsUniqueM (M ⊓ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) M
  six_charTwo : CharTwo (M ⊓ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G))
  six_reduced : IsTwoReducedIn (M ⊓ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) (V154 T Mc M)
  six_pCore : pCoreOf 2 (M ⊓ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) =
    T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)
  six_autOn : autOn (M ⊓ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) (V154 T Mc M) =
    autOn M (V154 T Mc M)
  six_hyp : ∀ H : Subgroup G, IsHStar T M H →
    Hyp315Base T M (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) H
      (V154 T Mc M) ∧ Hyp315.CaseII M H (V154 T Mc M)
  seven_normalizer : Subgroup.normalizer (T : Set G) ≤ M
  seven_minParabolic : ∀ H : Subgroup G, IsHStar T M H → H ∈ uFamHat ⊤ T

@[expose] def StageLemma1519 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma1519Concl T Mc M

@[expose] def StageLemma15110 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M →
    Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) 3 →
      Nonempty (↥(autOn M (V154 T Mc M)) ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2))

@[expose] def StageLemma15111 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → ∀ H : Subgroup G, IsHStar T M H →
      V154 T Mc M ≤ pCoreOf 2 H ∧ IsElemAbelian 2 (conjClosure (V154 T Mc M) H)

@[expose] def Lemma15113Three (T Mc M : Subgroup G) : Prop :=
  (∀ A : Subgroup G, IsElemAbelianCorank T 1 A → autOn A (V154 T Mc M) ≠ ⊥ →
      Nat.card (autOn A (V154 T Mc M)) = 2 ∧ autOn A (V154 T Mc M) ∈ QhatStarOn M (V154 T Mc M)) ∨
    Case1517Three M (V154 T Mc M) (mBar0 T Mc M)

@[expose] def Lemma15113Four (T Mc M : Subgroup G) : Prop :=
  (autOn (thompsonJi T 1) (V154 T Mc M) = autOn T (V154 T Mc M) ⊓ mBar0 T Mc M ∧
      autOn (thompsonJi M 1) (V154 T Mc M) = mBar0 T Mc M) ∨
    (Case1517Three M (V154 T Mc M) (mBar0 T Mc M) ∧
      Nat.card (autOn (thompsonJi T 1) (V154 T Mc M)) = 2)

structure Lemma15113Concl (T Mc M : Subgroup G) : Prop where
  one : ¬ Subgroup.centralizer (omegaOneCenterOf (thompsonJi T 1) : Set G) ≤ M
  two : ⁅V154 T Mc M, thompsonJi T 1⁆ ≠ ⊥
  three : Lemma15113Three T Mc M
  four : Lemma15113Four T Mc M

@[expose] def StageLemma15113 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma15113Concl T Mc M

@[expose] def StageLemma15113Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma15113Three T Mc M

@[expose] def StageLemma15113Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma15113Four T Mc M

@[expose] def Case3bOf (T Mc M : Subgroup G) : Prop :=
  Case1517Three M (V154 T Mc M) (mBar0 T Mc M) ∧
    autOn (thompsonJi T 1) (V154 T Mc M) ≠ autOn T (V154 T Mc M) ∧
    ¬ (Case1517Four T M (V154 T Mc M) (mBar0 T Mc M) ∨
      (∃ p : ℕ, (p = 3 ∨ p = 5) ∧ Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) p) ∨
      Case1517Seven T M (V154 T Mc M) (mBar0 T Mc M))

structure Lemma15114Concl (T Mc M : Subgroup G) : Prop where
  one : ¬ Case3bOf T Mc M →
    oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) :
        Subgroup G) : Set G)
  two : ¬ Case3bOf T Mc M →
    (M ⊓ Subgroup.normalizer (thompsonJi T 1 : Set G) ≤ Subgroup.normalizer
        ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) : Subgroup G) : Set G) ∧
      Subgroup.normalizer
        ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) : Subgroup G) : Set G) ≤ Mc)
  three : ¬ Case3bOf T Mc M → Subgroup.normalizer (thompsonJi T 1 : Set G) ≤ M ⊓ Mc

@[expose] def Step1514Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M →
    oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) :
        Subgroup G) : Set G) →
    ¬ oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) :
        Subgroup G) : Set G) →
    ¬ Case3bOf T Mc M →
    ∃ H : Subgroup G, IsHStar T M H ∧
      H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
      ¬ oTwoUpper H ≤ oTwoUpper (Subgroup.centralizer ((V154 T Mc M ⊓
        Subgroup.centralizer (thompsonJi T 1 : Set G) : Subgroup G) : Set G))

@[expose] def StageLemma15114 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma15114Concl T Mc M

@[expose] def cSecIn (F L N : Subgroup G) : Subgroup G :=
  Subgroup.closure {f | f ∈ F ∧ ∀ x ∈ N, f * x * f⁻¹ * x⁻¹ ∈ L}

@[expose] def fixSecIn (A L N : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ N ∧ ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ L}

@[expose] def QuotIsoWith (H C J : Subgroup G) (X Y : Type*) [Group X] [Group Y] : Prop :=
  ∃ φ : ↥H →* X, Function.Surjective φ ∧ φ.ker = C.subgroupOf H ∧
    Nonempty (↥((J.subgroupOf H).map φ) ≃* Y)

@[expose] def NaturalSn (n : ℕ) (F L X : Subgroup G) [(L.subgroupOf X).Normal] : Prop :=
  ∃ (θ : ↥F →* Equiv.Perm (Fin n)) (β : ↥(G6.coreMod n) →* ↥X ⧸ L.subgroupOf X),
    Function.Surjective θ ∧ θ.ker = (cSecIn F L X).subgroupOf F ∧
    Function.Surjective β ∧ β.ker = G6.natKer n ∧
    ∀ (f : ↥F) (u : ↥(G6.coreMod n)) (x : ↥X), β u = QuotientGroup.mk x →
      ∃ hfx : (f : G) * (x : G) * (f : G)⁻¹ ∈ X,
        β (G6.coreAct n (θ f) u) = QuotientGroup.mk ⟨(f : G) * (x : G) * (f : G)⁻¹, hfx⟩

@[expose] def NaturalSnPair (n : ℕ) (H L N : Subgroup G) : Prop :=
  ∃ (F₁ F₂ X₁ X₂ : Subgroup G) (_ : (L.subgroupOf X₁).Normal) (_ : (L.subgroupOf X₂).Normal),
    F₁ ≤ H ∧ F₂ ≤ H ∧ X₁ = ⁅N, F₁⁆ ⊔ L ∧ X₂ = ⁅N, F₂⁆ ⊔ L ∧ L ≤ X₁ ∧ X₁ ≤ N ∧ L ≤ X₂ ∧
    X₂ ≤ N ∧ X₁ ⊓ X₂ = L ∧ X₁ ⊔ X₂ = N ∧
    (∀ f ∈ F₂, ∀ x ∈ X₁, f * x * f⁻¹ * x⁻¹ ∈ L) ∧ (∀ f ∈ F₁, ∀ x ∈ X₂, f * x * f⁻¹ * x⁻¹ ∈ L) ∧
    F₁ ⊔ F₂ = thompsonJ H ⊔ cSecIn H L N ∧ NaturalSn n F₁ L X₁ ∧ NaturalSn n F₂ L X₂

@[expose] def ChiefFactorShape (H L N : Subgroup G) : Prop :=
  ∃ _ : (L.subgroupOf N).Normal,
    (QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3)) ∧
        NaturalSn 3 H L N) ∨
      (QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 5)) ∧
        NaturalSn 5 H L N) ∨
      (QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2))
          (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧ NaturalSnPair 3 H L N) ∨
      (QuotIsoWith H (cSecIn H L N) (thompsonJ H) (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))
          (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) ∧ NaturalSnPair 5 H L N)

@[expose] def IsMinOffender (T H V A : Subgroup G) : Prop :=
  IsMaxElemAbelian T A ∧ ¬ IsMaxElemAbelian (pCoreOf 2 H) A ∧
    (∀ A' : Subgroup G, IsMaxElemAbelian T A' → ¬ IsMaxElemAbelian (pCoreOf 2 H) A' →
      Nat.card ↥(A ⊔ pCoreOf 2 H) ≤ Nat.card ↥(A' ⊔ pCoreOf 2 H)) ∧
    ⁅⁅conjClosure V H, A⁆, A⁆ = ⊥

structure Concl319 (T M V H : Subgroup G) (hyp5 : Prop) : Prop where
  elemAbelian : IsElemAbelian 2 (conjClosure V H)
  chief : IsChiefSeriesFrom H (conjClosure V H) (conjClosure V H) 2
  exists_A : ∃ A : Subgroup G, IsMinOffender T H V A
  quadratic : ∀ A : Subgroup G, IsMinOffender T H V A →
    ⁅⁅conjClosure V H, A⁆, A⁆ = ⊥
  count_one : ∀ A : Subgroup G, IsMinOffender T H V A →
    Nat.card A ^ 2 * Nat.card (conjClosure V H ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) =
      Nat.card (A ⊓ pCoreOf 2 H : Subgroup G) ^ 2 * Nat.card (conjClosure V H)
  count_two : ∀ A : Subgroup G, IsMinOffender T H V A →
    Nat.card (conjClosure V H) *
        Nat.card (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G) :
          Subgroup G) ^ 2 =
      Nat.card (A ⊓ pCoreOf 2 H : Subgroup G) ^ 2 *
        Nat.card (conjClosure V H ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)
  count_three : ∀ A : Subgroup G, IsMinOffender T H V A → ∀ h ∈ H,
    ⁅A ⊓ pCoreOf 2 H, conjSubgroup V h⁆ ≠ ⊥ →
      Nat.card (A ⊓ pCoreOf 2 H : Subgroup G) ^ 2 *
          Nat.card (conjSubgroup V h ⊓ Subgroup.centralizer (A ⊓ pCoreOf 2 H : Set G) :
            Subgroup G) =
        Nat.card (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V h : Set G) :
          Subgroup G) ^ 2 * Nat.card (conjSubgroup V h)
  count_four : ∀ A : Subgroup G, IsMinOffender T H V A → ∀ L N : Subgroup G,
    IsChiefStep H (conjClosure V H) L N → ¬ IsCentralStep H L N →
      cSecIn A L N = A ⊓ pCoreOf 2 H ∧
        Nat.card A * Nat.card (fixSecIn A L N) =
          Nat.card (A ⊓ pCoreOf 2 H : Subgroup G) * Nat.card N
  fixed_eq : ∀ A : Subgroup G, IsMinOffender T H V A →
    conjClosure V H ⊓ Subgroup.centralizer (A : Set G) =
      conjClosure V H ⊓ Subgroup.centralizer (A ⊓ pCoreOf 2 H : Set G)
  shape : hyp5 → ∀ L N : Subgroup G, IsChiefStep H (conjClosure V H) L N →
    ¬ IsCentralStep H L N → ChiefFactorShape H L N

@[expose] def Lemma319Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315Base T M M₀ H V, Hyp315.CaseII M H V →
      qInt M₀ V h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V ≤ pCoreOf 2 H → ¬ IsDualFFOn M₀ V →
      Concl319 T M V H (oTwoUpper (M ⊓ Subgroup.centralizer
        (quasithinOmegaOneCenter T : Set G)) ≤ Subgroup.centralizer (V : Set G))

@[expose] def NotDualFF1512 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M →
    ¬ IsDualFFOn (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) (V154 T Mc M)

@[expose] def StageLemma15112Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → ∀ H : Subgroup G, IsHStar T M H →
      ⁅omegaOneCenterOf (thompsonJi T 1), oTwoUpper H⁆ = ⊥

@[expose] def StageLemma15112 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → ∀ H : Subgroup G, IsHStar T M H →
      Concl319 T M (V154 T Mc M) H True ∧
        ⁅omegaOneCenterOf (thompsonJi T 1), oTwoUpper H⁆ = ⊥

end Finite

end CFSG.Quasithin
