module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsF4Data
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAutMap
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.Quasithin.H13.Sec53F.ReeF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeCover
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Sec53F.BA CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

local notation "Γ₄" => F4.reeGamma K a
local notation "U₄" => F4.reeFixedPosUnipotent K a
local notation "H₄" => F4.reeFixedTorus K a
local notation "𝒰" => Subgroup.subgroupOf U₄ Γ₄
local notation "ℋ" => Subgroup.subgroupOf H₄ Γ₄
local notation "𝔽" => MonoidHom.range (F4.reeGammaFieldAutHom K a)

theorem f4_F_U : ∀ φ ∈ 𝔽, ∀ x : ↥Γ₄, φ x ∈ 𝒰 ↔ x ∈ 𝒰 := by
  rintro _ ⟨β, rfl⟩ x
  have h := (reeGammaFieldAut_mem_largeReeOppAut (a := a) β).1
  have hx := Subgroup.mem_map_iff_mem (f := (F4.reeGammaFieldAut K a β).toMonoidHom)
    (F4.reeGammaFieldAut K a β).injective (K := 𝒰) (x := x)
  rw [h] at hx
  exact hx

theorem f4_F_H : ∀ φ ∈ 𝔽, ∀ h ∈ ℋ, φ h ∈ ℋ := by
  rintro _ ⟨β, rfl⟩ h hh
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  refine Subgroup.mem_inf.2 ⟨?_, (F4.reeGammaFieldAut K a β h).2⟩
  have := entrywise_mem_torusGroup (σ := β) (Subgroup.mem_inf.1 hh).1
  rwa [← coe_reeGammaFieldAut (a := a)] at this

theorem f4_F_comm : ∀ φ ∈ 𝔽, ∀ ψ ∈ 𝔽, φ * ψ = ψ * φ := by
  rintro _ ⟨β, rfl⟩ _ ⟨γ, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact RingEquiv.ext fun c => ringEquiv_comm_of_finite γ β c

theorem entry_torusPair (β : K ≃+* K) (t u : Kˣ) :
    Units.map (entrywiseHom β.toRingHom) (torusPair a (t, u)) =
      torusPair a (Units.map β.toRingHom.toMonoidHom t, Units.map β.toRingHom.toMonoidHom u) := by
  rw [torusPair_apply, torusPair_apply, map_mul, map_mul, map_mul, entrywise_torusElt,
    entrywise_torusElt, entrywise_torusElt, entrywise_torusElt, map_pow, map_pow]

theorem sq_fixed_of_fixes_torus (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) (β : K ≃+* K)
    (hfix : ∀ h ∈ ℋ, F4.reeGammaFieldAutHom K a β h = h) (t : Kˣ) :
    β ((t : K) ^ 2) = (t : K) ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, htor, -⟩ :=
    large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨htu, hT, -⟩ := htor t 1
  have h1 : Units.map (entrywiseHom β.toRingHom) (torusPair a (t, 1)) = torusPair a (t, 1) :=
    congrArg (fun x : ↥Γ₄ => (x : ModGL F4.tag K)) (hfix ⟨_, htu⟩ (Subgroup.mem_subgroupOf.2 hT))
  rw [entry_torusPair, map_one] at h1
  have h2 := congrArg (fun A => A * largeReeA1X a 1 * A⁻¹) h1
  simp only [torusPair_conj_largeReeA1X] at h2
  have h3 := largeReeA1X_injective h2
  simpa using h3

theorem f4_F_faithful (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) :
    ∀ φ ∈ 𝔽, (∀ h ∈ ℋ, φ h = h) → φ = 1 := by
  rintro _ ⟨β, rfl⟩ hfix
  have hall : ∀ x : K, β x = x := by
    intro x
    obtain ⟨r, rfl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) x
    by_cases hr : r = 0
    · subst hr
      simp
    · simpa [sq] using sq_fixed_of_fixes_torus hK ha β hfix (Units.mk0 r hr)
  rw [show β = 1 from RingEquiv.ext hall, map_one]

theorem f4_normal_form (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) (α : MulAut ↥Γ₄)
    (hα : ∀ x, α x ∈ 𝒰 ↔ x ∈ 𝒰) :
    ∃ g ∈ Subgroup.normalizer ((𝒰 : Subgroup ↥Γ₄) : Set ↥Γ₄), ∃ φ ∈ 𝔽,
      α = MulAut.conj g * φ := by
  obtain ⟨⟨g, β⟩, hgβ, -⟩ :=
    (large_Ree_full_inner_field_automorphism_normal_form a ha K hK).2.1 α
  have hgβ' : α = MulAut.conj g * F4.reeGammaFieldAutHom K a β := hgβ
  refine ⟨g, ?_, F4.reeGammaFieldAutHom K a β, ⟨β, rfl⟩, hgβ'⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e : (MulAut.conj g) y = α ((F4.reeGammaFieldAutHom K a β)⁻¹ y) := by
    rw [hgβ', MulAut.mul_apply, MulAut.apply_inv_self]
  have h1 := hα ((F4.reeGammaFieldAutHom K a β)⁻¹ y)
  have h2 := f4_F_U (a := a) (F4.reeGammaFieldAutHom K a β) ⟨β, rfl⟩
    ((F4.reeGammaFieldAutHom K a β)⁻¹ y)
  rw [MulAut.apply_inv_self] at h2
  rw [← MulAut.conj_apply, e, h1]
  exact h2

theorem borelAutData_f4 (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) :
    BorelAutData 𝒰 ℋ 𝔽 :=
  { center := f4_center hK
    sylow := f4_sylow
    H_comm := f4_H_comm
    H_le := f4_H_le
    U_inf_H := f4_U_inf_H
    B_eq := f4_B_eq
    F_U := f4_F_U
    F_H := f4_F_H
    F_comm := f4_F_comm
    F_faithful := f4_F_faithful hK ha
    normal_form := fun α hα => f4_normal_form hK ha α hα }

end CFSG.Quasithin.H13.Sec53F.ReeF4

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Blueprint CFSG.LieType.Ree


set_option linter.unusedSectionVars false

theorem lieBorelFacts_f4 : LieBorelFacts .twistedF4 0 := by
  intro Y _ _ f hpar hY U hU
  obtain ⟨-, hX⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.reeTits_of_lieModel hY (by decide)
  have hS := ReeTag.large_Ree_model_Schreier Y 2 f hX
  obtain ⟨hadm, a, hfa, hmodel⟩ := hX
  have ha : 1 ≤ a := by have := hadm.2.2.2.2.2; omega
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hS.2.2.2.2.2 a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv _ E.toEquiv
  exact (ReeF4.borelAutData_f4 hK' ha).exists_of_equiv E hU

theorem lieAutFacts_f4 : LieAutFacts .twistedF4 0 :=
  lieAutFacts_of_lieBorelFacts lieBorelFacts_f4

end CFSG.Quasithin.H13.Sec53F
