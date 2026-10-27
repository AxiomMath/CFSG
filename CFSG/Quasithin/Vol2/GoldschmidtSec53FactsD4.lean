module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsD4Data
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAutMap
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
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

namespace CFSG.Quasithin.H13.Sec53F.TriD4

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Quasithin.H13.Sec53F.BA
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "U₀" => graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom
local notation "H₁" => graphFixedRootTorus TwistTag.D4 K σ.toRingHom
local notation "𝒰" => Subgroup.subgroupOf U₀ C₀
local notation "ℋ" => Subgroup.subgroupOf H₁ C₀
local notation "𝔽" => MonoidHom.range (fieldActorHom (t := TwistTag.D4) σ)

theorem d4_F_U : ∀ φ ∈ 𝔽, ∀ x : ↥C₀, φ x ∈ 𝒰 ↔ x ∈ 𝒰 := by
  rintro _ ⟨δ, rfl⟩ x
  have hδ : ∀ c, δ (σ c) = σ (δ c) := ringEquiv_comm_of_finite σ δ
  have hmap := map_units_map_entrywiseHom_graphFixedPosUnipotent (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) hδ
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  change Units.map (entrywiseHom δ.toRingHom) (x : ModGL TwistTag.D4.tag K) ∈ U₀ ↔ _
  constructor
  · intro h
    rw [← hmap] at h
    exact (Subgroup.mem_map_iff_mem (units_map_entrywiseHom_injective δ)).1 h
  · intro h
    have := Subgroup.mem_map_of_mem (Units.map (entrywiseHom δ.toRingHom)) h
    rwa [hmap] at this

theorem d4_F_H : ∀ φ ∈ 𝔽, ∀ h ∈ ℋ, φ h ∈ ℋ := by
  rintro _ ⟨δ, rfl⟩ h hh
  have hδ : ∀ c, δ (σ c) = σ (δ c) := ringEquiv_comm_of_finite σ δ
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  change Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.D4.tag K) ∈ H₁
  obtain ⟨hT, hG⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨hT1, hF⟩ := Subgroup.mem_inf.1 hT
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨entry_mem_torusGroup δ hT1,
    units_map_entrywiseHom_mem_twistedFixedGroup hδ hF⟩,
    units_map_entrywiseHom_mem_graphFixedRootGroup hδ hG⟩

theorem d4_F_comm : ∀ φ ∈ 𝔽, ∀ ψ ∈ 𝔽, φ * ψ = ψ * φ := by
  rintro _ ⟨δ, rfl⟩ _ ⟨ε, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact RingEquiv.ext fun c => ringEquiv_comm_of_finite ε δ c

theorem sq_fixed_of_fixes_torus (hσ3 : σ ^ 3 = 1) (δ : K ≃+* K)
    (hfix : ∀ h ∈ ℋ, fieldActorHom (t := TwistTag.D4) σ δ h = h) (a : Kˣ) :
    δ ((a : K) ^ 2) = (a : K) ^ 2 := by
  have hG := trialityTorusHom_mem_graphFixedRootGroup hσ3 (a, 1)
  have hmem : (⟨_, hG⟩ : ↥C₀) ∈ ℋ := Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2
    ⟨trialityTorusHom_mem_graphFixedTorus hσ3 (a, 1), hG⟩)
  have h1 := congrArg (fun x : ↥C₀ => (x : ModGL TwistTag.D4.tag K)) (hfix _ hmem)
  simp only [fieldActorHom_apply, coe_fieldActor] at h1
  have hone : trialityFixedUnit K σ 1 = 1 := map_one _
  rw [trialityTorusHom_apply, trialityOuter_mul_middle_eq, hone, entry_rootDiagUnit] at h1
  have h2 := congrFun (rootDiagUnit_injective h1) (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank)
  have h3 : Units.map δ.toRingHom.toMonoidHom (a ^ 2 * 1⁻¹) = a ^ 2 * 1⁻¹ := h2
  simpa using congrArg Units.val h3

theorem d4_F_faithful (hσ3 : σ ^ 3 = 1) [CharP K 2] :
    ∀ φ ∈ 𝔽, (∀ h ∈ ℋ, φ h = h) → φ = 1 := by
  rintro _ ⟨δ, rfl⟩ hfix
  have hall : ∀ x : K, δ x = x := by
    intro x
    obtain ⟨r, rfl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) x
    by_cases hr : r = 0
    · subst hr
      simp
    · simpa [sq] using sq_fixed_of_fixes_torus σ hσ3 δ hfix (Units.mk0 r hr)
  rw [show δ = 1 from RingEquiv.ext hall, map_one]

theorem d4_normal_form {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (α : MulAut ↥C₀) (hα : ∀ x, α x ∈ 𝒰 ↔ x ∈ 𝒰) :
    ∃ g ∈ Subgroup.normalizer ((𝒰 : Subgroup ↥C₀) : Set ↥C₀), ∃ φ ∈ 𝔽, α = MulAut.conj g * φ := by
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := (even_triality_exact_automorphism_normal_form hf K hK σ hσ).2.1 α
  have hgδ' : α = MulAut.conj g * fieldActorHom (t := TwistTag.D4) σ δ := hgδ
  refine ⟨g, ?_, fieldActorHom (t := TwistTag.D4) σ δ, ⟨δ, rfl⟩, hgδ'⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e : (MulAut.conj g) y = α ((fieldActorHom (t := TwistTag.D4) σ δ)⁻¹ y) := by
    rw [hgδ', MulAut.mul_apply, MulAut.apply_inv_self]
  have h1 := hα ((fieldActorHom (t := TwistTag.D4) σ δ)⁻¹ y)
  have h2 := d4_F_U σ (fieldActorHom (t := TwistTag.D4) σ δ) ⟨δ, rfl⟩
    ((fieldActorHom (t := TwistTag.D4) σ δ)⁻¹ y)
  rw [MulAut.apply_inv_self] at h2
  rw [← MulAut.conj_apply, e, h1]
  exact h2

theorem borelAutData_d4 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) : BorelAutData 𝒰 ℋ 𝔽 := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  have hσ3 : σ ^ 3 = 1 :=
    RingEquiv.ext fun c => (ringEquiv_pow_three_apply σ c).trans (ringEquiv_cube_apply_eq hK hσ c)
  exact
    { center := d4_center σ
      sylow := d4_sylow σ
      H_comm := d4_H_comm σ
      H_le := d4_H_le σ
      U_inf_H := d4_U_inf_H σ
      B_eq := d4_B_eq σ
      F_U := d4_F_U σ
      F_H := d4_F_H σ
      F_comm := d4_F_comm σ
      F_faithful := d4_F_faithful σ hσ3
      normal_form := fun α hα => d4_normal_form σ hf hK hσ α hα }

end CFSG.Quasithin.H13.Sec53F.TriD4

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Setup.X6


set_option linter.unusedSectionVars false

theorem lieBorelFacts_d4 : LieBorelFacts .trialityD4 0 := by
  intro Y _ _ f hpar hY U hU
  obtain ⟨-, hX⟩ := CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hY
    (by decide)
  obtain ⟨hf, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  exact (TriD4.borelAutData_d4 σ hf hK hσ).exists_of_equiv e hU

theorem lieAutFacts_d4 : LieAutFacts .trialityD4 0 :=
  lieAutFacts_of_lieBorelFacts lieBorelFacts_d4

end CFSG.Quasithin.H13.Sec53F
