module

public import CFSG.RankThree.PartTwo.Sec18.Item185Ctx
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRem
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.GroupTheory.PCore.Transport
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.Extremal
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemHc
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemRank
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.RankThree.PartTwo.Sec19.Steps195
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import Certificates.Certificate43
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G] [Finite G]

private def GoodElt (M J : Subgroup G) (p : ℕ) (y : G) : Prop :=
  y ∈ J ∧ (∃ N : ℕ, y ^ (p ^ N) ∈ CFSG.Open.pCoreOf 2 M) ∧
    (∃ k ∈ J, y * k * y⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M) ∧
    (∀ k ∈ J, y ^ p * k * (y ^ p)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M)

private theorem exists_pElt_of_isQuasisimple {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ u : X, u ∉ Subgroup.center X ∧ u ^ p ∈ Subgroup.center X ∧
      ∃ N : ℕ, u ^ (p ^ N) = 1 := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hX
  have h3 : 2 < (Nat.card (X ⧸ Subgroup.center X)).primeFactors.card := by
    by_contra h
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr
      (CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
        (by omega)) a b)
  obtain ⟨p, hpmem, hp23⟩ : ∃ p ∈ (Nat.card (X ⧸ Subgroup.center X)).primeFactors,
      p ∉ ({2, 3} : Finset ℕ) := by
    by_contra h
    push Not at h
    have h1 := Finset.card_le_card (show (Nat.card (X ⧸ Subgroup.center X)).primeFactors ⊆
      {2, 3} from h)
    have h2 : ({2, 3} : Finset ℕ).card = 2 := by decide
    omega
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hp3 : 3 < p := by
    have h2 := hp.two_le
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp23
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (Nat.dvd_of_mem_primeFactors hpmem)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
  refine ⟨p, hp, hp3, x ^ (ordCompl[p] (orderOf x)), fun hmem => ?_, ?_,
    (orderOf x).factorization p, ?_⟩
  · have h1 : ((x ^ ordCompl[p] (orderOf x) : X) : X ⧸ Subgroup.center X) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    rw [QuotientGroup.mk_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hz] at h2
    exact Nat.not_dvd_ordCompl hp hn h2
  · rw [← QuotientGroup.eq_one_iff, ← pow_mul, QuotientGroup.mk_pow, mul_comm, pow_mul, ← hz,
      pow_orderOf_eq_one, one_pow]
  · rw [← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self, pow_orderOf_eq_one]

private theorem coe_mem_pCoreOf_of_mem_pCore {M : Subgroup G} {L : Subgroup M}
    (hL : L.IsSubnormal) {ℓ : L} (hℓ : ℓ ∈ CFSG.pCore 2 L) :
    ((ℓ : M) : G) ∈ CFSG.Open.pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (ℓ : M) ∈ CFSG.Open.pCore 2 M :=
    CFSG.RankThree.PartTwo.Late.pCoreOf_le_pCore_of_isSubnormal 2 hL
      (Subgroup.mem_map_of_mem L.subtype hℓ)
  exact Subgroup.mem_map_of_mem M.subtype h1

private theorem mem_pCore_of_coe_mem_pCoreOf {M : Subgroup G} {L : Subgroup M} {ℓ : L}
    (hℓ : ((ℓ : M) : G) ∈ CFSG.Open.pCoreOf 2 M) : ℓ ∈ CFSG.pCore 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : (ℓ : M) ∈ CFSG.pCore 2 M := by
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hℓ
    rwa [show x = (ℓ : M) from Subtype.ext hxe] at hx
  have hT : (CFSG.pCore 2 M).comap L.subtype ≤ CFSG.pCore 2 L :=
    CFSG.LieType.BorelTits.le_pCore 2
      ((CFSG.LieType.BorelTits.pCore_normal 2).comap L.subtype)
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2).comap_of_injective L.subtype
        L.subtype_injective)
  exact hT hmem

private theorem exists_goodElt_of_mem {M K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ y : G, GoodElt M K p y := by
  obtain ⟨hKM, -, hsn, hq⟩ := mem_oTwoComponentsIn_iff.mp hK
  obtain ⟨p, hp, hp3, u, hu, hup, N, huN⟩ := exists_pElt_of_isQuasisimple hq
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective u
  have hcoe : ∀ ℓ' : K.subgroupOf M, ((ℓ' : M) : G) ∈ K :=
    fun ℓ' => Subgroup.mem_subgroupOf.mp ℓ'.2
  refine ⟨p, hp, hp3, ((ℓ : M) : G), hcoe ℓ, ⟨N, ?_⟩, ?_, fun k hk => ?_⟩
  · have h1 : ℓ ^ (p ^ N) ∈ CFSG.pCore 2 (K.subgroupOf M) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact huN
    simpa using coe_mem_pCoreOf_of_mem_pCore hsn h1
  · rw [Subgroup.mem_center_iff] at hu
    push Not at hu
    obtain ⟨κ, hκ⟩ := hu
    obtain ⟨κ', rfl⟩ := QuotientGroup.mk_surjective κ
    refine ⟨((κ' : M) : G), hcoe κ', fun hmem => hκ ?_⟩
    have h1 : ℓ * κ' * ℓ⁻¹ * κ'⁻¹ ∈ CFSG.pCore 2 (K.subgroupOf M) :=
      mem_pCore_of_coe_mem_pCoreOf (by simpa using hmem)
    rw [← QuotientGroup.eq_one_iff] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    exact ((commutatorElement_eq_one_iff_mul_comm.mp
      (by rw [commutatorElement_def]; exact h1))).symm
  · set κ' : K.subgroupOf M := ⟨⟨k, hKM hk⟩, Subgroup.mem_subgroupOf.mpr hk⟩
    have h1 : ℓ ^ p * κ' * (ℓ ^ p)⁻¹ * κ'⁻¹ ∈ CFSG.pCore 2 (K.subgroupOf M) := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
      rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hup _).symm
    simpa using coe_mem_pCoreOf_of_mem_pCore hsn h1

private theorem dvd_of_zpow_mem {Y : Type*} [Group Y] {H : Subgroup Y} {u : Y} {p N : ℕ}
    (hp : p.Prime) (hN : u ^ (p ^ N) = 1) (hu : u ∉ H) {x : ℤ} (hx : u ^ x ∈ H) :
    (p : ℤ) ∣ x := by
  rw [Int.natCast_dvd]
  by_contra hpx
  have hn : u ^ x.natAbs ∈ H := by
    rcases Int.natAbs_eq x with h | h
    · rw [h, zpow_natCast] at hx
      exact hx
    · rw [h, zpow_neg, zpow_natCast] at hx
      exact inv_mem_iff.mp hx
  have hcop : Nat.Coprime x.natAbs (orderOf u) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hN)
      (Nat.Coprime.pow_right N (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpx)))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact hu (by rw [← hm]; exact H.pow_mem hn m)

private theorem exists_elemAbelian_of_pow_mem {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (A C : Subgroup Y) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hpow : ∀ g ∈ A, g ^ p ∈ C) :
    ∃ E : Subgroup Y, CFSG.Open.IsElemAbelian p E ∧ (C.subgroupOf A).index ≤ Nat.card E := by
  have hAc' : ∀ a b : A, a * b = b * a := fun a b => Subtype.ext (hAc a a.2 b b.2)
  let ψ : A →* A := MonoidHom.mk' (fun g => g ^ p) (fun a b => Commute.mul_pow (hAc' a b) p)
  have hψ : ∀ g, ψ g = g ^ p := fun g => rfl
  have hrange : ψ.range ≤ C.subgroupOf A := by
    intro _ hg
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hg
    rw [Subgroup.mem_subgroupOf, hψ, Subgroup.coe_pow]
    exact hpow g g.2
  refine ⟨ψ.ker.map A.subtype, ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext ?_, ?_⟩, ?_⟩
  · exact hAc _ (Subgroup.map_subtype_le _ a.2) _ (Subgroup.map_subtype_le _ b.2)
  · rintro _ ⟨g, hg, rfl⟩
    have h1 : g ^ p = 1 := by rw [← hψ]; exact MonoidHom.mem_ker.mp hg
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, h1, Subgroup.coe_one]
  · rw [Subgroup.card_map_of_injective A.subtype_injective]
    have h1 := Subgroup.card_ker_mul_card_range ψ
    have h2 := Subgroup.card_mul_index (C.subgroupOf A)
    have h3 := Subgroup.card_le_of_le hrange
    have h4 : 0 < Nat.card (C.subgroupOf A) := Nat.card_pos
    have h5 : Nat.card (C.subgroupOf A) * (C.subgroupOf A).index ≤
        Nat.card (C.subgroupOf A) * Nat.card ψ.ker := by
      rw [h2, ← h1, mul_comm (Nat.card ψ.ker)]
      exact Nat.mul_le_mul_right _ h3
    exact Nat.le_of_mul_le_mul_left h5 h4

private theorem le_index_of_three {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (A C : Subgroup Y)
    {v₁ v₂ v₃ : Y} (h₁ : v₁ ∈ A) (h₂ : v₂ ∈ A) (h₃ : v₃ ∈ A) (c₁₂ : Commute v₁ v₂)
    (c₁₃ : Commute v₁ v₃) (c₂₃ : Commute v₂ v₃)
    (hind : ∀ x y z : ℤ, v₁ ^ x * v₂ ^ y * v₃ ^ z ∈ C → (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z) :
    p ^ 3 ≤ (C.subgroupOf A).index := by
  have key : ∀ a b c a' b' c' : ℤ, (v₁ ^ a * v₂ ^ b * v₃ ^ c)⁻¹ * (v₁ ^ a' * v₂ ^ b' * v₃ ^ c') =
      v₁ ^ (a' - a) * v₂ ^ (b' - b) * v₃ ^ (c' - c) := by
    intro a b c a' b' c'
    have k₁ : Commute (v₂ ^ (-b)) (v₁ ^ (a' - a)) := (c₁₂.zpow_zpow _ _).symm
    have k₂ : Commute (v₃ ^ (-c)) (v₁ ^ (a' - a) * v₂ ^ (b' - b)) :=
      ((c₁₃.zpow_zpow _ _).mul_left (c₂₃.zpow_zpow _ _)).symm
    calc (v₁ ^ a * v₂ ^ b * v₃ ^ c)⁻¹ * (v₁ ^ a' * v₂ ^ b' * v₃ ^ c')
        = v₃ ^ (-c) * (v₂ ^ (-b) * v₁ ^ (a' - a)) * v₂ ^ b' * v₃ ^ c' := by group
      _ = v₃ ^ (-c) * (v₁ ^ (a' - a) * v₂ ^ (-b)) * v₂ ^ b' * v₃ ^ c' := by rw [k₁.eq]
      _ = v₃ ^ (-c) * (v₁ ^ (a' - a) * v₂ ^ (b' - b)) * v₃ ^ c' := by group
      _ = v₁ ^ (a' - a) * v₂ ^ (b' - b) * v₃ ^ (-c) * v₃ ^ c' := by rw [k₂.eq]
      _ = v₁ ^ (a' - a) * v₂ ^ (b' - b) * v₃ ^ (c' - c) := by group
  have hmemA : ∀ a b c : ℤ, v₁ ^ a * v₂ ^ b * v₃ ^ c ∈ A := fun a b c =>
    A.mul_mem (A.mul_mem (A.zpow_mem h₁ a) (A.zpow_mem h₂ b)) (A.zpow_mem h₃ c)
  have hfin : ∀ a a' : Fin p, (p : ℤ) ∣ ((a' : ℕ) : ℤ) - ((a : ℕ) : ℤ) → a = a' := by
    intro a a' h
    have ha := a.isLt
    have ha' := a'.isLt
    have h0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    exact Fin.ext (by omega)
  let F : Fin p × Fin p × Fin p → A ⧸ C.subgroupOf A := fun t =>
    ((⟨_, hmemA (t.1 : ℕ) (t.2.1 : ℕ) (t.2.2 : ℕ)⟩ : A) : A ⧸ C.subgroupOf A)
  have hF : Function.Injective F := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ heq
    have hmem := QuotientGroup.eq.mp heq
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hmem
    rw [key] at hmem
    obtain ⟨hx, hy, hz⟩ := hind _ _ _ hmem
    rw [hfin a a' hx, hfin b b' hy, hfin c c' hz]
  calc p ^ 3 = Nat.card (Fin p × Fin p × Fin p) := by
        rw [Nat.card_prod, Nat.card_prod, Nat.card_fin]
        ring
    _ ≤ Nat.card (A ⧸ C.subgroupOf A) := Nat.card_le_card_of_injective F hF
    _ = (C.subgroupOf A).index := (Subgroup.index_eq_card _).symm

private theorem exists_elemAbelian_of_three {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) {v₁ v₂ v₃ : Y} {H₁ H₂ H₃ : Subgroup Y}
    (c₁₂ : Commute v₁ v₂) (c₁₃ : Commute v₁ v₃) (c₂₃ : Commute v₂ v₃)
    (hv₁ : v₁ ∉ H₁) (hv₂ : v₂ ∉ H₂) (hv₃ : v₃ ∉ H₃)
    (hN₁ : ∃ N : ℕ, v₁ ^ (p ^ N) = 1) (hN₂ : ∃ N : ℕ, v₂ ^ (p ^ N) = 1)
    (hN₃ : ∃ N : ℕ, v₃ ^ (p ^ N) = 1)
    (hp₁ : v₁ ^ p ∈ H₁) (hp₂ : v₂ ^ p ∈ H₂) (hp₃ : v₃ ^ p ∈ H₃)
    (h₂₁ : v₂ ∈ H₁) (h₃₁ : v₃ ∈ H₁) (h₁₂ : v₁ ∈ H₂) (h₃₂ : v₃ ∈ H₂) (h₁₃ : v₁ ∈ H₃)
    (h₂₃ : v₂ ∈ H₃) :
    ∃ E : Subgroup Y, CFSG.Open.IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  obtain ⟨N₁, hN₁⟩ := hN₁
  obtain ⟨N₂, hN₂⟩ := hN₂
  obtain ⟨N₃, hN₃⟩ := hN₃
  have hind : ∀ x y z : ℤ, v₁ ^ x * v₂ ^ y * v₃ ^ z ∈ H₁ ⊓ H₂ ⊓ H₃ →
      (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
    intro x y z h
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at h
    obtain ⟨⟨g₁, g₂⟩, g₃⟩ := h
    refine ⟨dvd_of_zpow_mem hp hN₁ hv₁ ?_, dvd_of_zpow_mem hp hN₂ hv₂ ?_,
      dvd_of_zpow_mem hp hN₃ hv₃ ?_⟩
    · have e : v₁ ^ x = v₁ ^ x * v₂ ^ y * v₃ ^ z * v₃ ^ (-z) * v₂ ^ (-y) := by group
      rw [e]
      exact H₁.mul_mem (H₁.mul_mem g₁ (H₁.zpow_mem h₃₁ _)) (H₁.zpow_mem h₂₁ _)
    · have e : v₂ ^ y = v₁ ^ (-x) * (v₁ ^ x * v₂ ^ y * v₃ ^ z) * v₃ ^ (-z) := by group
      rw [e]
      exact H₂.mul_mem (H₂.mul_mem (H₂.zpow_mem h₁₂ _) g₂) (H₂.zpow_mem h₃₂ _)
    · have e : v₃ ^ z = v₂ ^ (-y) * v₁ ^ (-x) * (v₁ ^ x * v₂ ^ y * v₃ ^ z) := by group
      rw [e]
      exact H₃.mul_mem (H₃.mul_mem (H₃.zpow_mem h₂₃ _) (H₃.zpow_mem h₁₃ _)) g₃
  have hpw : ({v₁, v₂, v₃} : Set Y).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption | exact Commute.symm ‹_›
  have hAc : ∀ a ∈ Subgroup.closure ({v₁, v₂, v₃} : Set Y),
      ∀ b ∈ Subgroup.closure ({v₁, v₂, v₃} : Set Y), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.mp (Subgroup.isMulCommutative_closure hpw)
      ⟨a, ha⟩ ⟨b, hb⟩)
  have hpow : ∀ g ∈ Subgroup.closure ({v₁, v₂, v₃} : Set Y), g ^ p ∈ H₁ ⊓ H₂ ⊓ H₃ := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx <;> rw [hx]
      · exact ⟨⟨hp₁, H₂.pow_mem h₁₂ p⟩, H₃.pow_mem h₁₃ p⟩
      · exact ⟨⟨H₁.pow_mem h₂₁ p, hp₂⟩, H₃.pow_mem h₂₃ p⟩
      · exact ⟨⟨H₁.pow_mem h₃₁ p, H₂.pow_mem h₃₂ p⟩, hp₃⟩
    | one => rw [one_pow]; exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      rw [(show Commute x y from hAc x hx y hy).mul_pow]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx =>
      rw [inv_pow]
      exact Subgroup.inv_mem _ ihx
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_of_pow_mem _ _ hAc hpow
  exact ⟨E, hE, (le_index_of_three _ _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) c₁₂ c₁₃ c₂₃
    hind).trans hcard⟩

private theorem mk_eq_one_iff {M : Subgroup G} (m : M) :
    QuotientGroup.mk' (CFSG.pCore 2 M) m = 1 ↔ (m : G) ∈ CFSG.Open.pCoreOf 2 M := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, CFSG.mem_openPCoreOf_iff]

private theorem mk_comm_iff {M : Subgroup G} (a b : M) :
    QuotientGroup.mk' (CFSG.pCore 2 M) a * QuotientGroup.mk' (CFSG.pCore 2 M) b =
        QuotientGroup.mk' (CFSG.pCore 2 M) b * QuotientGroup.mk' (CFSG.pCore 2 M) a ↔
      (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  have h := mk_eq_one_iff (a * b * a⁻¹ * b⁻¹)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  exact h

private theorem image_le_centralizer {M J K : Subgroup G} (hJ : J ∈ oTwoComponentsIn M)
    (hK : K ∈ oTwoComponentsIn M) (hne : J ≠ K) :
    (J.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 M)) ≤
      Subgroup.centralizer ((K.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 M)) :
        Set (M ⧸ CFSG.pCore 2 M)) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  exact Sec19.Step1910Proof.mk_mul_comm_of_ne hK hJ hne.symm (Subgroup.mem_subgroupOf.mp hk)
    (Subgroup.mem_subgroupOf.mp hg)

private theorem goodElt_image {M J : Subgroup G} (hJ : J ∈ oTwoComponentsIn M) {p : ℕ} {y : G}
    (hy : GoodElt M J p y) :
    ∃ u : M ⧸ CFSG.pCore 2 M, u ∈ (J.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 M)) ∧
      u ∉ Subgroup.centralizer ((J.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 M)) :
        Set (M ⧸ CFSG.pCore 2 M)) ∧
      u ^ p ∈ Subgroup.centralizer ((J.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 M)) :
        Set (M ⧸ CFSG.pCore 2 M)) ∧
      ∃ N : ℕ, u ^ (p ^ N) = 1 := by
  obtain ⟨hyJ, ⟨N, hN⟩, ⟨k, hkJ, hk⟩, hpow⟩ := hy
  have hJM := le_of_mem_oTwoComponentsIn hJ
  refine ⟨QuotientGroup.mk' (CFSG.pCore 2 M) ⟨y, hJM hyJ⟩,
    ⟨⟨y, hJM hyJ⟩, Subgroup.mem_subgroupOf.mpr hyJ, rfl⟩, ?_, ?_, N, ?_⟩
  · intro hc
    apply hk
    have h1 := Subgroup.mem_centralizer_iff.mp hc _
      ⟨⟨k, hJM hkJ⟩, Subgroup.mem_subgroupOf.mpr hkJ, rfl⟩
    exact (mk_comm_iff ⟨y, hJM hyJ⟩ ⟨k, hJM hkJ⟩).mp h1.symm
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_pow]
    refine ((mk_comm_iff (⟨y, hJM hyJ⟩ ^ p) m).mpr ?_).symm
    rw [Subgroup.coe_pow]
    exact hpow _ (Subgroup.mem_subgroupOf.mp hm)
  · rw [← map_pow, mk_eq_one_iff, Subgroup.coe_pow]
    exact hN

private theorem exists_lift_of_quotient {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (M ⧸ CFSG.pCore 2 M)} (hE : CFSG.Open.IsElemAbelian p E) :
    ∃ T : Subgroup G, T ≤ M ∧ CFSG.Open.IsElemAbelian p T ∧ Nat.card T = Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : p.Coprime (Nat.card (QuotientGroup.mk' (CFSG.pCore 2 M)).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := M)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  obtain ⟨R, -, ⟨e⟩⟩ := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup p hp
    (QuotientGroup.mk' (CFSG.pCore 2 M)) (QuotientGroup.mk'_surjective _) hker E hE.isPGroup
  have hR : CFSG.Open.IsElemAbelian p R :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport p E R e.symm hE
  refine ⟨R.map M.subtype, Subgroup.map_subtype_le R, hR.map M.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective M.subtype_injective]
  exact Nat.card_congr e.toEquiv

private theorem false_of_three_goodElt {A M : Subgroup G} (h : Sec18Std G A M) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {J₁ J₂ J₃ : Subgroup G}
    (hJ₁ : J₁ ∈ oTwoComponentsIn M) (hJ₂ : J₂ ∈ oTwoComponentsIn M)
    (hJ₃ : J₃ ∈ oTwoComponentsIn M) (h₁₂ : J₁ ≠ J₂) (h₁₃ : J₁ ≠ J₃) (h₂₃ : J₂ ≠ J₃)
    {y₁ y₂ y₃ : G} (hy₁ : GoodElt M J₁ p y₁) (hy₂ : GoodElt M J₂ p y₂)
    (hy₃ : GoodElt M J₃ p y₃) : False := by
  obtain ⟨u₁, hu₁, hu₁c, hu₁p, hu₁N⟩ := goodElt_image hJ₁ hy₁
  obtain ⟨u₂, hu₂, hu₂c, hu₂p, hu₂N⟩ := goodElt_image hJ₂ hy₂
  obtain ⟨u₃, hu₃, hu₃c, hu₃p, hu₃N⟩ := goodElt_image hJ₃ hy₃
  have c₂₁ := image_le_centralizer hJ₂ hJ₁ h₁₂.symm hu₂
  have c₃₁ := image_le_centralizer hJ₃ hJ₁ h₁₃.symm hu₃
  have c₁₂ := image_le_centralizer hJ₁ hJ₂ h₁₂ hu₁
  have c₃₂ := image_le_centralizer hJ₃ hJ₂ h₂₃.symm hu₃
  have c₁₃ := image_le_centralizer hJ₁ hJ₃ h₁₃ hu₁
  have c₂₃ := image_le_centralizer hJ₂ hJ₃ h₂₃ hu₂
  have k₁₂ : Commute u₁ u₂ := Subgroup.mem_centralizer_iff.mp c₂₁ u₁ hu₁
  have k₁₃ : Commute u₁ u₃ := Subgroup.mem_centralizer_iff.mp c₃₁ u₁ hu₁
  have k₂₃ : Commute u₂ u₃ := Subgroup.mem_centralizer_iff.mp c₃₂ u₂ hu₂
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_of_three hp k₁₂ k₁₃ k₂₃ hu₁c hu₂c hu₃c hu₁N hu₂N
    hu₃N hu₁p hu₂p hu₃p c₂₁ c₃₁ c₁₂ c₃₂ c₁₃ c₂₃
  obtain ⟨T, hTM, hTa, hTcard⟩ := exists_lift_of_quotient hp (by omega) hE
  have h1 := card_le_sq_of_le_M h hp hp3 hTM hTa
  have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

private theorem goodElt_conj {M K : Subgroup G} {p : ℕ} {y g : G} (hg : g ∈ M)
    (hy : GoodElt M K p y) : GoodElt M (K.map (MulAut.conj g).toMonoidHom) p (g * y * g⁻¹) := by
  unfold GoodElt at hy ⊢
  obtain ⟨hyK, ⟨N, hN⟩, ⟨k, hk, hnc⟩, hcen⟩ := hy
  have hgN : g ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg
  have key : ∀ x : G, g * x * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M ↔ x ∈ CFSG.Open.pCoreOf 2 M :=
    fun x => (Subgroup.mem_normalizer_iff.mp hgN x).symm
  refine ⟨Subgroup.mem_map.mpr ⟨y, hyK, by simp [MulAut.conj_apply]⟩, ⟨N, ?_⟩,
    ⟨g * k * g⁻¹, Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply]⟩, ?_⟩, ?_⟩
  · rw [conj_pow]
    exact (key _).mpr hN
  · intro h
    have e : g * y * g⁻¹ * (g * k * g⁻¹) * (g * y * g⁻¹)⁻¹ * (g * k * g⁻¹)⁻¹ =
        g * (y * k * y⁻¹ * k⁻¹) * g⁻¹ := by group
    rw [e] at h
    exact hnc ((key _).mp h)
  · intro k' hk'
    obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk'
    have e : (g * y * g⁻¹) ^ p * (MulAut.conj g).toMonoidHom k₀ * ((g * y * g⁻¹) ^ p)⁻¹ *
        ((MulAut.conj g).toMonoidHom k₀)⁻¹ = g * (y ^ p * k₀ * (y ^ p)⁻¹ * k₀⁻¹) * g⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_pow]
      group
    rw [e]
    exact (key _).mpr (hcen k₀ hk₀)

private theorem map_conj_mul (K : Subgroup G) (a b : G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_eq_iff_mem (K : Subgroup G) (a b : G) :
    K.map (MulAut.conj b).toMonoidHom = K.map (MulAut.conj a).toMonoidHom ↔
      a⁻¹ * b ∈ Subgroup.normalizer (K : Set G) := by
  have key := map_conj_mul K a (a⁻¹ * b)
  rw [mul_inv_cancel_left] at key
  have hinj : Function.Injective (MulAut.conj a).toMonoidHom :=
    fun x y h => (MulAut.conj a).injective h
  rw [key, (Subgroup.map_injective hinj).eq_iff]
  constructor
  · intro h
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  · intro h
    exact CFSG.RankThree.PartTwo.Late.map_conj_eq_of_mem_normalizer h

private theorem index_inf_normalizer_le {M K U : Subgroup G} (hUM : U ≤ M) :
    ((U ⊓ Subgroup.normalizer (K : Set G)).subgroupOf U).index ≤
      {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom}.ncard := by
  have hmem : ∀ a b : U, a⁻¹ * b ∈ (U ⊓ Subgroup.normalizer (K : Set G)).subgroupOf U ↔
      (a : G)⁻¹ * (b : G) ∈ Subgroup.normalizer (K : Set G) := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨U.mul_mem (U.inv_mem a.2) b.2, h⟩⟩
  let f : U → {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom} :=
    fun u => ⟨K.map (MulAut.conj (u : G)).toMonoidHom, (u : G), hUM u.2, rfl⟩
  have hf : ∀ a b : U, a⁻¹ * b ∈ (U ⊓ Subgroup.normalizer (K : Set G)).subgroupOf U →
      f a = f b := by
    intro a b hab
    exact Subtype.ext ((map_conj_eq_iff_mem K (a : G) (b : G)).mpr ((hmem a b).mp hab)).symm
  let F : U ⧸ (U ⊓ Subgroup.normalizer (K : Set G)).subgroupOf U →
      {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom} :=
    Quotient.lift f (fun a b hab => hf a b (QuotientGroup.leftRel_apply.mp hab))
  have hF : Function.Injective F := by
    rintro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : K.map (MulAut.conj (a : G)).toMonoidHom =
        K.map (MulAut.conj (b : G)).toMonoidHom :=
      congrArg Subtype.val hxy
    exact QuotientGroup.eq.mpr
      ((hmem a b).mpr ((map_conj_eq_iff_mem K (a : G) (b : G)).mp h1.symm))
  rw [Subgroup.index, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective F hF

theorem ncard_conj_le_two {A M : Subgroup G} (h : Sec18Std G A M) {K : Subgroup G}
    (hK : K ∈ oTwoComponentsIn M) :
    {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom}.ncard ≤ 2 := by
  by_contra hcon
  have h2 : 2 < {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom}.ncard := by
    omega
  obtain ⟨K₁, K₂, K₃, ⟨g₁, hg₁, rfl⟩, ⟨g₂, hg₂, rfl⟩, ⟨g₃, hg₃, rfl⟩, h₁₂, h₁₃, h₂₃⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mp h2
  obtain ⟨p, hp, hp3, y, hy⟩ := exists_goodElt_of_mem hK
  exact false_of_three_goodElt h hp hp3 (map_conj_mem_oTwoComponentsIn hK hg₁)
    (map_conj_mem_oTwoComponentsIn hK hg₂) (map_conj_mem_oTwoComponentsIn hK hg₃)
    h₁₂ h₁₃ h₂₃ (goodElt_conj hg₁ hy) (goodElt_conj hg₂ hy) (goodElt_conj hg₃ hy)

theorem le_normalizer_of_ncard_le_two {M K : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    {P : Subgroup G} (hP : IsPGroup 3 P) (hPM : P ≤ M)
    (h2 : {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom}.ncard ≤ 2) :
    P ≤ Subgroup.normalizer (K : Set G) := by
  have hidx := (index_inf_normalizer_le (K := K) hPM).trans h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd : ((P ⊓ Subgroup.normalizer (K : Set G)).subgroupOf P).index ∣ 3 ^ k := by
    rw [← hk]
    apply Subgroup.index_dvd_card
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hle : 3 ^ i ≤ 2 := hi ▸ hidx
  have hi0 : i = 0 := by
    by_contra hne
    have h3 : 3 ≤ 3 ^ i := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hne)
    exact absurd (le_trans h3 hle) (by norm_num)
  have h1 : ((P ⊓ Subgroup.normalizer (K : Set G)).subgroupOf P).index = 1 := by
    rw [hi, hi0, pow_zero]
  rw [Subgroup.index_eq_one] at h1
  intro x hx
  have hmem : (⟨x, hx⟩ : P) ∈ (P ⊓ Subgroup.normalizer (K : Set G)).subgroupOf P := by
    rw [h1]
    exact Subgroup.mem_top _
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2

private theorem irr_three_le_index {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ} {a b c : Γ}
    (hab : a⁻¹ * b ∉ S) (hac : a⁻¹ * c ∉ S) (hbc : b⁻¹ * c ∉ S) : 3 ≤ S.index := by
  let F : Fin 3 → Γ ⧸ S := ![(a : Γ ⧸ S), (b : Γ ⧸ S), (c : Γ ⧸ S)]
  have hF : Function.Injective F := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (QuotientGroup.eq.mp hij) hab
    · exact absurd (QuotientGroup.eq.mp hij) hac
    · exact absurd (QuotientGroup.eq.mp hij.symm) hab
    · rfl
    · exact absurd (QuotientGroup.eq.mp hij) hbc
    · exact absurd (QuotientGroup.eq.mp hij.symm) hac
    · exact absurd (QuotientGroup.eq.mp hij.symm) hbc
    · rfl
  have h := Nat.card_le_card_of_injective F hF
  simpa [Subgroup.index] using h

private theorem irr_dichotomy {Kc R : Subgroup G} (hR : (R.subgroupOf Kc).index ≤ 2) {k₀ k : G}
    (hk₀ : k₀ ∈ Kc) (hk : k ∈ Kc) (hk₀R : k₀ ∉ R) : k ∈ R ∨ k₀⁻¹ * k ∈ R := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hkR, hk₀kR⟩ := hcon
  have h3 : 3 ≤ (R.subgroupOf Kc).index :=
    irr_three_le_index (a := (1 : Kc)) (b := ⟨k₀, hk₀⟩) (c := ⟨k, hk⟩)
      (by simpa [Subgroup.mem_subgroupOf] using hk₀R)
      (by simpa [Subgroup.mem_subgroupOf] using hkR)
      (by simpa [Subgroup.mem_subgroupOf] using hk₀kR)
  omega

private theorem irr_quaternion_exists {Γ : Type} [Group Γ] {Φ ΦR : Subgroup Γ}
    (g : QuaternionGroup 2 →* Γ) (hg : Function.Injective g) (hΦ : ∀ x, g x ∈ Φ)
    (hdich : ∀ σ ∈ Φ, ∀ τ ∈ Φ, σ ∉ ΦR → τ ∈ ΦR ∨ σ⁻¹ * τ ∈ ΦR) :
    ∃ x : QuaternionGroup 2, g x ∈ ΦR ∧ g x ^ 2 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsq : ∀ x : QuaternionGroup 2, x ^ 2 ≠ 1 → g x ^ 2 ≠ 1 := by
    intro x hx h
    apply hx
    apply hg
    rw [map_pow, h, map_one]
  have hi2 : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
  have hj2 : (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
  have hij2 : ((QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0) ^ 2 ≠ 1 := by
    decide
  have hgi : g (QuaternionGroup.a 1) ∉ ΦR := fun h => hsq _ hi2 (hcon _ h)
  have hgj : g (QuaternionGroup.xa 0) ∉ ΦR := fun h => hsq _ hj2 (hcon _ h)
  have hgij : g (QuaternionGroup.a 1 * QuaternionGroup.xa 0) ∉ ΦR :=
    fun h => hsq _ hij2 (hcon _ h)
  have hr : (g (QuaternionGroup.a 1))⁻¹ * g (QuaternionGroup.xa 0) ∈ ΦR := by
    rcases hdich _ (hΦ (QuaternionGroup.a 1)) _ (hΦ (QuaternionGroup.xa 0)) hgi with h | h
    · exact absurd h hgj
    · exact h
  have hii : g (QuaternionGroup.a 1) * g (QuaternionGroup.a 1) ∈ ΦR := by
    rcases hdich _ (hΦ (QuaternionGroup.a 1)) _
        (Φ.mul_mem (hΦ (QuaternionGroup.a 1)) (hΦ (QuaternionGroup.a 1))) hgi with h | h
    · exact h
    · rw [inv_mul_cancel_left] at h
      exact absurd h hgi
  have hprod : g (QuaternionGroup.a 1 * QuaternionGroup.xa 0) ∈ ΦR := by
    rw [map_mul]
    have e : g (QuaternionGroup.a 1) * g (QuaternionGroup.xa 0) =
        (g (QuaternionGroup.a 1) * g (QuaternionGroup.a 1)) *
          ((g (QuaternionGroup.a 1))⁻¹ * g (QuaternionGroup.xa 0)) := by group
    rw [e]
    exact ΦR.mul_mem hii hr
  exact hgij hprod

private theorem irr_isElemAbelian_inf {X : Subgroup G} (hX : CFSG.Assembly.IsElemAbelian 3 X)
    (L : Subgroup G) : CFSG.Assembly.IsElemAbelian 3 (X ⊓ L) :=
  ⟨⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from
      congrArg (Subtype.val : X → G) (hX.1.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩))⟩⟩,
    fun x hx => hX.2 x hx.1⟩

private theorem irr_pow_apply {X : Subgroup G} {k : G} (hN : k ∈ Subgroup.normalizer (X : Set G))
    (n : ℕ) (x : X) : ((X.normalizerMonoidHom ⟨k, hN⟩ ^ n) x : G) = k ^ n * x * (k ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, Sec4.normalizerMonoidHom_apply_coe, ih]
    group

private theorem irr_pow_eq_one_iff {X : Subgroup G} {k : G}
    (hN : k ∈ Subgroup.normalizer (X : Set G)) (n : ℕ) :
    X.normalizerMonoidHom ⟨k, hN⟩ ^ n = 1 ↔ ∀ x : X, k ^ n * x * (k ^ n)⁻¹ = x := by
  constructor
  · intro h x
    have hx := irr_pow_apply hN n x
    rw [h, MulAut.one_apply] at hx
    exact hx.symm
  · intro h
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [irr_pow_apply hN n y, MulAut.one_apply]
    exact h y

theorem isIrreducibleOn_normalizer_inf {A M H : Subgroup G} {c : G} {P : Subgroup G}
    (hC : Ctx G A M H c P) {K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) :
    Sec21.IsIrreducibleOn (Sec4.autIn (Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (K : Set G)) (A ⊓ inSubgroup perfectResidual H)) := by
  have hstd : Sec18Std G A M := hC.toSec18H.toSec18Std
  have hP := hC.planeQ8
  set Kc : Subgroup G := lc H c ⊓ Subgroup.normalizer (A : Set G) with hKc
  set B : Subgroup G := A ⊓ inSubgroup perfectResidual H with hB
  set R : Subgroup G := Kc ⊓ Subgroup.normalizer (K : Set G) with hR
  have hBA : B ≤ A := inf_le_left
  have hKcM : Kc ≤ M :=
    (inf_le_right : Kc ≤ Subgroup.normalizer (A : Set G)).trans (Rem187QProof.normalizer_le hstd)
  have hidx : (R.subgroupOf Kc).index ≤ 2 :=
    (index_inf_normalizer_le (K := K) hKcM).trans (ncard_conj_le_two hstd hK)
  have hBab : CFSG.Assembly.IsElemAbelian 3 B :=
    irr_isElemAbelian_inf hP.isElemAbelian (inSubgroup perfectResidual H)
  have hB9 : Nat.card B = 9 := hP.card_plane
  obtain ⟨f, hf⟩ := hP.quaternion
  set g : QuaternionGroup 2 →* MulAut A := (Sec4.autIn Kc A).subtype.comp f with hg
  have hΦ : ∀ y, g y ∈ Sec4.autIn Kc A := fun y => (f y).2
  have hginj : Function.Injective g := Subtype.val_injective.comp hf
  have hdich : ∀ σ ∈ Sec4.autIn Kc A, ∀ τ ∈ Sec4.autIn Kc A, σ ∉ Sec4.autIn R A →
      τ ∈ Sec4.autIn R A ∨ σ⁻¹ * τ ∈ Sec4.autIn R A := by
    intro σ hσ τ hτ hσR
    obtain ⟨k₀, hk₀N, hk₀Kc, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    obtain ⟨k, hkN, hkKc, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
    have hk₀R : k₀ ∉ R := fun h => hσR (Sec4.mem_autIn_iff.mpr ⟨k₀, hk₀N, h, rfl⟩)
    rcases irr_dichotomy hidx hk₀Kc hkKc hk₀R with h | h
    · exact Or.inl (Sec4.mem_autIn_iff.mpr ⟨k, hkN, h, rfl⟩)
    · refine Or.inr (Sec4.mem_autIn_iff.mpr ⟨k₀⁻¹ * k, ?_, h, ?_⟩)
      · exact (Subgroup.normalizer (A : Set G)).mul_mem
          ((Subgroup.normalizer (A : Set G)).inv_mem hk₀N) hkN
      · rw [← map_inv, ← map_mul]
        rfl
  obtain ⟨x, hxR, hx2⟩ := irr_quaternion_exists g hginj hΦ hdich
  have hx4all : ∀ y : QuaternionGroup 2, y ^ 4 = 1 := by decide
  have h4x : g x ^ 4 = 1 := by rw [← map_pow, hx4all x, map_one]
  obtain ⟨r, hrN, hrR, hrx⟩ := Sec4.mem_autIn_iff.mp hxR
  have hrKc : r ∈ Kc := (Subgroup.mem_inf.mp hrR).1
  have hrK : r ∈ Subgroup.normalizer (K : Set G) := (Subgroup.mem_inf.mp hrR).2
  have hrB : r ∈ Subgroup.normalizer (B : Set G) := hP.le_normalizer_plane hrKc
  have hrc : Commute r c := hP.commute r hrKc
  have hcomm2 : Commute (r ^ 2) c := hrc.pow_left 2
  have h4 : (B.normalizerMonoidHom ⟨r, hrB⟩) ^ 4 = 1 := by
    rw [irr_pow_eq_one_iff hrB 4]
    have hA4 : ∀ a : A, r ^ 4 * a * (r ^ 4)⁻¹ = a := by
      rw [← hrx] at h4x
      exact (irr_pow_eq_one_iff hrN 4).mp h4x
    intro b
    exact hA4 ⟨b, hBA b.2⟩
  have h2 : (B.normalizerMonoidHom ⟨r, hrB⟩) ^ 2 ≠ 1 := by
    intro h2eq
    rw [irr_pow_eq_one_iff hrB 2] at h2eq
    have hAZ : A ≤ Subgroup.centralizer ({r ^ 2} : Set G) := by
      rw [hP.eq_sup]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hcomm2.eq
      · intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have this : r ^ 2 * b * (r ^ 2)⁻¹ = b := h2eq ⟨b, hb⟩
        calc r ^ 2 * b = r ^ 2 * b * (r ^ 2)⁻¹ * r ^ 2 := by group
          _ = b * r ^ 2 := by rw [this]
    have hA2 : ∀ a : A, r ^ 2 * a * (r ^ 2)⁻¹ = a := by
      intro a
      have h' := Subgroup.mem_centralizer_iff.mp (hAZ a.2) (r ^ 2) (Set.mem_singleton _)
      rw [h', mul_inv_cancel_right]
    apply hx2
    rw [← hrx]
    exact (irr_pow_eq_one_iff hrN 2).mpr hA2
  exact Sec13.isIrreducibleOn_of_order_four hBab hB9
    (show B.normalizerMonoidHom ⟨r, hrB⟩ ∈ Sec4.autIn (Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (K : Set G)) B from
      Sec4.mem_autIn_iff.mpr ⟨r, hrB, Subgroup.mem_inf.mpr ⟨hrN, hrK⟩, rfl⟩) h4 h2

theorem normalizer_le_normalizer_component {M K B : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    (hBK : B ≤ K) (hnc : ∃ b ∈ B, ∃ k ∈ K, b * k * b⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M) :
    M ⊓ Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  rintro x ⟨hxM, hxB⟩
  have hK' : K.map (MulAut.conj x).toMonoidHom ∈ oTwoComponentsIn M :=
    map_conj_mem_oTwoComponentsIn hK hxM
  have hBK' : B ≤ K.map (MulAut.conj x).toMonoidHom := by
    intro b hb
    have hk : x⁻¹ * b * x ∈ B := by
      refine (Subgroup.mem_normalizer_iff.mp hxB (x⁻¹ * b * x)).mpr ?_
      have e : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
      rw [e]
      exact hb
    exact ⟨x⁻¹ * b * x, hBK hk, by
      show x * (x⁻¹ * b * x) * x⁻¹ = b
      group⟩
  obtain ⟨b, hbB, k, hkK, hcomm⟩ := hnc
  have heq : K.map (MulAut.conj x).toMonoidHom = K := by
    by_contra hne
    exact hcomm (CFSG.RankThree.PartTwo.Sec19.Step1910Proof.commutator_mem_pCoreOf hK' hK hne
      (hBK' hbB) hkK)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
