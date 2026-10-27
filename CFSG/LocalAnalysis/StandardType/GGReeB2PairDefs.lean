module

public import CFSG.Quasithin.Background.SmithB45SzIrr
public import CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin.B45Sz
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

@[expose] noncomputable def szD (K : Type) [Field K] (m : ℕ) :
    Kˣ →* suzukiGroup m K :=
  MonoidHom.mk' (suzukiDElt m K) fun l l' => (suzukiDElt_mul l l').symm

structure SzPairDatum (K : Type) [Field K] (m : ℕ) (Γ : Type)
    [Group Γ] where
  φ₁ : suzukiGroup m K →* Γ
  φ₂ : suzukiGroup m K →* Γ
  comm : ∀ x y, φ₁ x * φ₂ y = φ₂ y * φ₁ x
  U : Subgroup Γ
  Ub : Subgroup Γ
  pgroup : IsPGroup 2 U
  Ub_le : Ub ≤ U
  up₁ : ∀ x ∈ szUp m K, φ₁ x ∈ U
  up₂ : ∀ x ∈ szUp m K, φ₂ x ∈ U
  Ub_norm : ∀ x, ∀ u ∈ Ub, φ₁ x * u * (φ₁ x)⁻¹ ∈ Ub
  T_norm : ∀ l₁ l₂ : Kˣ, ∀ u ∈ U,
    (φ₁ (szD K m l₁) * φ₂ (szD K m l₂)) * u * (φ₁ (szD K m l₁) * φ₂ (szD K m l₂))⁻¹ ∈ U
  na : Γ
  na_sq : na * na = 1
  na_conj : ∀ l₁ l₂ : Kˣ, na⁻¹ * (φ₁ (szD K m l₁) * φ₂ (szD K m l₂)) * na =
    φ₁ (szD K m ((l₂ / l₁) ^ 2 ^ m)) * φ₂ (szD K m ((l₁ * l₂) ^ 2 ^ m))
  na_up₁ : ∀ x ∈ szUp m K, na * φ₁ x * na⁻¹ ∈ Ub
  na_up₂ : ∀ x ∈ szUp m K, na * φ₂ x * na⁻¹ ∈ Ub

@[expose] noncomputable def SzPairDatum.tau {K : Type} [Field K]
    {m : ℕ} {Γ : Type} [Group Γ] (𝔇 : SzPairDatum K m Γ) : Kˣ × Kˣ →* Γ :=
  MonoidHom.noncommCoprod (𝔇.φ₁.comp (szD K m)) (𝔇.φ₂.comp (szD K m))
    fun a b => 𝔇.comm (szD K m a) (szD K m b)

theorem SzPairDatum.tau_apply {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] (𝔇 : SzPairDatum K m Γ) (l₁ l₂ : Kˣ) :
    𝔇.tau (l₁, l₂) = 𝔇.φ₁ (szD K m l₁) * 𝔇.φ₂ (szD K m l₂) := by
  rfl

@[expose] noncomputable def wchar1 {K : Type} [Field K] {m : ℕ} (k : Type) [Field k] [Algebra K k]
    (x : ZMod (2 ^ (2 * m + 1) - 1)) : Kˣ →* kˣ :=
  (Units.map (algebraMap K k : K →* k)) ^ x.val

@[expose] noncomputable def wchar {K : Type} [Field K] {m : ℕ} (k : Type) [Field k] [Algebra K k]
    (x y : ZMod (2 ^ (2 * m + 1) - 1)) : Kˣ × Kˣ →* kˣ :=
  ((wchar1 (K := K) k x).comp (MonoidHom.fst Kˣ Kˣ)) *
    ((wchar1 (K := K) k y).comp (MonoidHom.snd Kˣ Kˣ))

@[expose] def SzPairDatum.wt {K : Type} [Field K] {m : ℕ} {Γ : Type}
    [Group Γ] (k : Type) [Field k] [Algebra K k] {W : Type} [AddCommGroup W] [Module k W]
    (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W) :
    Set (ZMod (2 ^ (2 * m + 1) - 1) × ZMod (2 ^ (2 * m + 1) - 1)) :=
  {p | weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k p.1 p.2) ≠ ⊥}

instance neZero_two_pow_sub_one (m : ℕ) : NeZero (2 ^ (2 * m + 1) - 1) :=
  ⟨by have := Nat.one_lt_two_pow (n := 2 * m + 1) (by omega); omega⟩

theorem wchar1_apply {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type) [Field k]
    [Algebra K k] (x : ZMod (2 ^ (2 * m + 1) - 1)) (l : Kˣ) :
    ((wchar1 (K := K) k x l : kˣ) : k) = algebraMap K k (l : K) ^ x.val := by
  simp [wchar1]

theorem wchar_apply {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type) [Field k]
    [Algebra K k] (x y : ZMod (2 ^ (2 * m + 1) - 1)) (l₁ l₂ : Kˣ) :
    wchar (K := K) k x y (l₁, l₂) = wchar1 (K := K) k x l₁ * wchar1 (K := K) k y l₂ := rfl

theorem unit_pow_card_sub_one {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (l : Kˣ) :
    l ^ (2 ^ (2 * m + 1) - 1) = 1 := by
  classical
  have h : Fintype.card Kˣ = 2 ^ (2 * m + 1) - 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  rw [← h]
  exact pow_card_eq_one

theorem wchar1_add {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type) [Field k]
    [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1)) (x y : ZMod (2 ^ (2 * m + 1) - 1)) :
    wchar1 (K := K) k (x + y) = wchar1 (K := K) k x * wchar1 (K := K) k y := by
  ext l
  have h1 : ∀ n : ℕ, ((Units.map (algebraMap K k : K →* k) l) ^ (n % (2 ^ (2 * m + 1) - 1)) : kˣ) =
      (Units.map (algebraMap K k : K →* k) l) ^ n := by
    intro n
    have h2 : (Units.map (algebraMap K k : K →* k) l) ^ (2 ^ (2 * m + 1) - 1) = 1 := by
      rw [← map_pow, unit_pow_card_sub_one hK, map_one]
    exact (pow_eq_pow_mod n h2).symm
  simp only [wchar1, MonoidHom.pow_apply, MonoidHom.mul_apply, ZMod.val_add, h1]
  rw [pow_add]

theorem wchar1_pow {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type) [Field k]
    [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1)) (x : ZMod (2 ^ (2 * m + 1) - 1)) (n : ℕ)
    (l : Kˣ) : wchar1 (K := K) k x (l ^ n) = wchar1 (K := K) k ((n : ZMod _) * x) l := by
  have h1 : ∀ t : ℕ, ((Units.map (algebraMap K k : K →* k) l) ^ (t % (2 ^ (2 * m + 1) - 1)) : kˣ) =
      (Units.map (algebraMap K k : K →* k) l) ^ t := by
    intro t
    have h2 : (Units.map (algebraMap K k : K →* k) l) ^ (2 ^ (2 * m + 1) - 1) = 1 := by
      rw [← map_pow, unit_pow_card_sub_one hK, map_one]
    exact (pow_eq_pow_mod t h2).symm
  have h3 : (Units.map (algebraMap K k : K →* k) l) ^ (n % (2 ^ (2 * m + 1) - 1) * x.val) =
      ((Units.map (algebraMap K k : K →* k) l) ^ n) ^ x.val := by
    rw [pow_mul, h1 n]
  simp only [wchar1, MonoidHom.pow_apply, map_pow, ZMod.val_mul, ZMod.val_natCast, h1]
  rw [h3, ← pow_mul, ← pow_mul, mul_comm]

end CFSG.StandardType.ReeB2Fixed
