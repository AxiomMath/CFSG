module

public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

section Finite

variable [Finite G]

structure Setting152 (T Mc M : Subgroup G) : Prop where
  qtfe : quasithinQTFE14Cat G T Mc
  mf : IsMf T Mc M
  ce : IsCE1513 T M

open Classical in
@[expose] noncomputable def QsetOn (X V : Subgroup G) : Set (Subgroup (MulAut V)) :=
  if hV : IsElemAbelian 2 V then @Qset ↥V (commGroupOfElemAbelian hV) (autOn X V) else ∅

@[expose] def IsSmallQuot152 (X : Subgroup G) : Prop :=
  Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (OTwoQuot X ≃* DihedralGroup 5) ∨
    Nonempty (OTwoQuot X ≃* ↥(CFSG.Open.Sz 0))

@[expose] def IsSmallGroup152 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (X ≃* DihedralGroup 5) ∨
    Nonempty (X ≃* ↥(CFSG.Open.Sz 0))

@[expose] def lambdaOf (X : Subgroup G) : Subgroup G := Subgroup.closure {x | x ∈ X ∧ orderOf x = 2}

@[expose] def rcOf (Mc M : Subgroup G) : Subgroup G := pCoreOf 2 (Mc ⊓ M)

@[expose] noncomputable def yOf152 (T Mc M : Subgroup G) : Subgroup G :=
  oTwoUpper (conjClosure (rcOf Mc M) (oTwoUpper (m0Of T Mc M) ⊔ T))

@[expose] def InvertsOn {X : Type*} [Group X] (B A : Subgroup X) : Prop :=
  ∀ b ∈ B, b ≠ 1 → ∀ a ∈ A, b * a * b⁻¹ = a⁻¹

@[expose] def IsZ3TimesZ3Pow (n : ℕ) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod (3 ^ n)))

@[expose] def deltaSet (H V : Subgroup G) : Set (Subgroup G) :=
  {A | IsMaxElemAbelian H A ∧ ¬ A ≤ pCoreOf 2 H ∧
    (∀ A' : Subgroup G, IsMaxElemAbelian H A' → ¬ A' ≤ pCoreOf 2 H →
      Nat.card ↥(A ⊔ pCoreOf 2 H) ≤ Nat.card ↥(A' ⊔ pCoreOf 2 H)) ∧
    ⁅⁅conjClosure V H, A⁆, A⁆ = ⊥}

@[expose] def sigmaSet (H V : Subgroup G) : Set (Subgroup G) :=
  {B | ∃ A ∈ deltaSet H V, B = A ⊓ pCoreOf 2 H}

@[expose] def sigmaPrime (T H V : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ sigmaSet H V ∧ ¬ ∃ A ∈ deltaSet H V, A ≤ T ∧ B = A ⊓ pCoreOf 2 H}

structure IsHPair (H V H₁ H₂ : Subgroup G) : Prop where
  le₁ : pCoreOf 2 H ≤ H₁ ∧ H₁ ≤ H
  le₂ : pCoreOf 2 H ≤ H₂ ∧ H₂ ≤ H
  iso₁ : Nonempty (↥(imageOTwoQuot H H₁) ≃* Equiv.Perm (Fin 3))
  iso₂ : Nonempty (↥(imageOTwoQuot H H₂) ≃* Equiv.Perm (Fin 3))
  comm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 H
  inf_eq : H₁ ⊓ H₂ = pCoreOf 2 H
  swap : ∃ t ∈ H, t ^ 2 ∈ pCoreOf 2 H ∧ conjSub t H₁ = H₂ ∧ H = (H₁ ⊔ H₂) ⊔ Subgroup.zpowers t
  delta_le : ∀ A ∈ deltaSet H V, A ≤ H₁ ∨ A ≤ H₂

@[expose] def Case15213ii (T Mc M H : Subgroup G) : Prop :=
  Case1517Three M (V154 T Mc M) (mBar0 T Mc M) ∧
    ∀ B ∈ sigmaPrime T H (V154 T Mc M), oddCoreIn (autOn M (V154 T Mc M)) =
      ⁅oddCoreIn (autOn M (V154 T Mc M)), autOn B (V154 T Mc M)⁆

@[expose] def IsB0 (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) : Prop :=
  B₀ ≤ autOn T (V154 T Mc M) ∧ Nat.card B₀ = 2 ∧
    oddCoreIn (autOn M (V154 T Mc M)) = ⁅oddCoreIn (autOn M (V154 T Mc M)), B₀⁆

@[expose] noncomputable def zSOf (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) : Subgroup G :=
  ⁅V154 T Mc M, preOn T (V154 T Mc M) B₀⁆

@[expose] noncomputable def sOf152 (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) : Subgroup G :=
  T ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)

structure Hyp15215 (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) (I : Subgroup G) :
    Prop where
  inH : InH (Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)) I
  not_le : ¬ I ≤ Mc

@[expose] def Hyp15215.Min (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (I : Subgroup G) : Prop :=
  Hyp15215 T Mc M B₀ I ∧ ∀ I' : Subgroup G,
    InH (Subgroup.centralizer (zSOf T Mc M B₀ : Set G)) I' → ¬ I' ≤ Mc → I' ≤ I → I' = I

@[expose] def Concl15218i (Mc M I : Subgroup G) : Prop := M ⊓ I ≤ Mc ⊓ I

@[expose] def Concl15218ii (T Mc M H : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (I : Subgroup G) : Prop :=
  ¬ M ⊓ I ≤ Mc ⊓ I ∧ Case15213ii T Mc M H ∧ IsOmegaFourPlusOn M (V154 T Mc M) ∧
    ∃ Z₁ : Subgroup G, Z₁ ⊔ quasithinOmegaOneCenter T = zSOf T Mc M B₀ ∧
      Z₁ ⊓ quasithinOmegaOneCenter T = ⊥ ∧
      M ⊓ I = M ⊓ Subgroup.centralizer (Z₁ : Set G) ∧ (M ⊓ I).relIndex M = 6

end Finite

end CFSG.Quasithin
