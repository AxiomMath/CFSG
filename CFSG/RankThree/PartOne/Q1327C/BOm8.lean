module

public import CFSG.RankThree.PartOne.Q1327C.BOm8Data
public import CFSG.RankThree.PartOne.Q1327C.BDefs
public import CFSG.RankThree.PartOne.K159H.O3Link
public import CFSG.RankThree.PartOne.KFR4.Row4
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.KF.R10Final
public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.RankThree.PartOne.Q1327C.BBase
public import CFSG.RankThree.PartOne.Q1327C.BRows
public import CFSG.RankThree.PartOne.Q1327C.P5Glue
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate9130

public section

namespace CFSG.RankThree.PartOne.Q1327C

open QuadraticMap CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFR4
  CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.S15K CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin (quadMinus)

theorem mem_normalizer_of_equiv {Y Γ : Type*} [Group Y] [Group Γ] (ψ : Y ≃* Γ) {E : Subgroup Y}
    {T : Subgroup Γ} (hψ : E.map ψ.toMonoidHom = T) {w : Γ}
    (hw : w ∈ Subgroup.normalizer (T : Set Γ)) : ψ.symm w ∈ Subgroup.normalizer (E : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hw ⊢
  intro y
  have hmem : ∀ z : Y, z ∈ E ↔ ψ z ∈ T := fun z => by
    rw [← hψ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [hmem y, hmem, map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]
  exact hw (ψ y)

theorem exists_b3_split {Y : Type} [Group Y] {f : ℕ} (hf : 1 ≤ f) {b c : GaloisField 2 f}
    (hbc : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0)
    (φ₀ : Y ≃* projOmegaMinus 3 (GaloisField 2 f) b c) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f - 1) (E : Subgroup Y) (hEcard : Nat.card E = p ^ 3)
    (hEexp : ∀ x ∈ E, x ^ p = 1) (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ (Γ : Type) (_ : Group Γ) (T : Subgroup Γ) (_ : B3Data p T) (ψ : Y ≃* Γ),
      E.map ψ.toMonoidHom = T := by
  have : NeZero f := ⟨by omega⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hpq
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (GaloisField 2 f)ˣ, IsPrimitiveRoot ζ p := by
    have h1 : p ∣ Nat.card (GaloisField 2 f)ˣ := by rw [Nat.card_units]; exact hpK
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h1
    exact ⟨x, by simpa [hx] using IsPrimitiveRoot.orderOf x⟩
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hK]
    have hpos : 0 < 2 ^ f - 1 := by
      have : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    have := Nat.le_of_dvd hpos hpq
    omega
  obtain ⟨A, _, _, _, qA, hreg, hani, hdim, ψ, hψ⟩ :=
    K159H.exists_tail_model hbc φ₀ hp (by omega) hζ E hEcard hEexp hEcomm
  exact ⟨↥(K159H.Om qA 3), inferInstance, K159H.Tg qA hζ,
    K159H.b3Data hp h4 hreg hani hdim hζ, ψ, hψ⟩

theorem exists_b3_nonsplit {Y : Type} [Group Y] {f : ℕ} (hf : 1 ≤ f) {b c : GaloisField 2 f}
    (hbc : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0)
    (φ₀ : Y ≃* projOmegaMinus 3 (GaloisField 2 f) b c) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) (E : Subgroup Y) (hEcard : Nat.card E = p ^ 3)
    (hEexp : ∀ x ∈ E, x ^ p = 1) (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ (Γ : Type) (_ : Group Γ) (T : Subgroup Γ) (_ : B3Data p T) (ψ : Y ≃* Γ),
      E.map ψ.toMonoidHom = T := by
  have : NeZero f := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpq' : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK]; exact hpq
  have hQ := polar_nondegenerate_quadMinus hbc
  have hdim : Module.finrank (GaloisField 2 f)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hV : ¬ IsPlusType (quadMinus 4 (GaloisField 2 f) b c) :=
    not_isPlusType_quadMinus (by omega) hbc
  let ψ : Y ≃* orthDerived (quadMinus 4 (GaloisField 2 f) b c) :=
    (φ₀.trans (projOmegaMinusEquivOrth (GaloisField 2 f) b c)).trans
      (orthDerivedEquivProj hQ).symm
  let θ : Y →* ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f)) :=
    (orthDerived (quadMinus 4 (GaloisField 2 f) b c)).subtype.comp ψ.toMonoidHom
  have hθinj : Function.Injective θ :=
    (orthDerived (quadMinus 4 (GaloisField 2 f) b c)).subtype_injective.comp ψ.injective
  have hcard : Nat.card (E.map θ) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective hθinj]
    exact hEcard
  have hexp : ∀ g ∈ E.map θ, g ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hEexp x hx, map_one]
  have hcomm : ∀ g ∈ E.map θ, ∀ g' ∈ E.map θ, g * g' = g' * g := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hEcomm x hx y hy]
  have hO : E.map θ ≤ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField 2 f) b c) := by
    rintro _ ⟨x, -, rfl⟩
    exact (Subgroup.commutator_le.mpr fun g hg g' hg' => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')) (ψ x).2
  obtain ⟨Ee, _, _, _, S, Φ, hΦ⟩ :=
    exists_frame (quadMinus 4 (GaloisField 2 f) b c) hQ hdim hV hp hp5 hpq' (E.map θ) hO hcard
      hexp hcomm
  let ψ' : Y ≃* ↥(Om S.D) := ψ.trans (orthDerivedEquiv Φ.symm)
  have hcoe : ∀ x : Y, (ψ' x : ↥(Om S.D)).1 = linConj Φ.toLinearEquiv.symm (θ x) := fun x => rfl
  have key : E.map ψ'.toMonoidHom = TS S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : θ x ∈ (Tstd S).map (linConj Φ.toLinearEquiv).toMonoidHom := by
        rw [hΦ]
        exact ⟨x, hx, rfl⟩
      obtain ⟨t, ht, htx⟩ := h1
      show (ψ' x : ↥(Om S.D)).1 ∈ Tstd S
      rw [hcoe, ← htx]
      show linConj Φ.toLinearEquiv.symm (linConj Φ.toLinearEquiv t) ∈ Tstd S
      rw [linConj_symm_linConj]
      exact ht
    · intro hy
      have h1 : linConj Φ.toLinearEquiv (y : ↥(Om S.D)).1 ∈ E.map θ := by
        rw [← hΦ]
        exact ⟨_, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := h1
      refine ⟨x, hx, Subtype.ext ?_⟩
      show (ψ' x : ↥(Om S.D)).1 = (y : ↥(Om S.D)).1
      rw [hcoe, show θ x = linConj Φ.toLinearEquiv (y : ↥(Om S.D)).1 from hxy,
        linConj_symm_linConj]
  exact ⟨↥(Om S.D), inferInstance, TS S, stdB3Data S, ψ', key⟩

theorem exists_signed_perm_data {Y : Type} [Group Y] {f : ℕ} (hf : 1 ≤ f) {b c : GaloisField 2 f}
    (hbc : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0)
    (φ₀ : Y ≃* projOmegaMinus 3 (GaloisField 2 f) b c) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) (E : Subgroup Y) (hEcard : Nat.card E = p ^ 3)
    (hEexp : ∀ x ∈ E, x ^ p = 1) (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ (e : Fin 3 → Y) (w : Fin 3 → Y) (u : Y), (∀ j, e j ∈ E) ∧
      (∀ a b c : ℤ, e 0 ^ a * e 1 ^ b * e 2 ^ c = 1 →
        (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c) ∧
      (∀ i, w i ∈ Subgroup.normalizer (E : Set Y)) ∧ u ∈ Subgroup.normalizer (E : Set Y) ∧
      (∀ i j, w i * e j * (w i)⁻¹ = if i = j then (e j)⁻¹ else e j) ∧
      u * e 0 * u⁻¹ = e 1 ∧ u * e 1 * u⁻¹ = e 0 ∧ u * e 2 * u⁻¹ = e 2 := by
  obtain ⟨Γ, _, T, D, ψ, hψ⟩ : ∃ (Γ : Type) (_ : Group Γ) (T : Subgroup Γ) (_ : B3Data p T)
      (ψ : Y ≃* Γ), E.map ψ.toMonoidHom = T := by
    rcases hpq with h | h
    · exact exists_b3_split hf hbc φ₀ hp hp5 h E hEcard hEexp hEcomm
    · exact exists_b3_nonsplit hf hbc φ₀ hp hp5 h E hEcard hEexp hEcomm
  obtain ⟨e, w, u, heT, hind, hwN, huN, hwe, hu0, hu1, hu2⟩ := signed_perm_of_b3 hp D
  have hmem : ∀ z : Y, z ∈ E ↔ ψ z ∈ T := fun z => by
    rw [← hψ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  refine ⟨fun j => ψ.symm (e j), fun i => ψ.symm (w i), ψ.symm u, fun j => ?_, ?_,
    fun i => mem_normalizer_of_equiv ψ hψ (hwN i), mem_normalizer_of_equiv ψ hψ huN, ?_, ?_, ?_, ?_⟩
  · rw [hmem, MulEquiv.apply_symm_apply]
    exact heT j
  · intro a b c' h
    apply hind a b c'
    have := congrArg ψ h
    simpa [map_mul, map_zpow] using this
  · intro i j
    apply ψ.injective
    have := hwe i j
    split_ifs at this ⊢
    · simpa [map_mul, map_inv] using this
    · simpa [map_mul, map_inv] using this
  · apply ψ.injective
    simpa [map_mul, map_inv] using hu0
  · apply ψ.injective
    simpa [map_mul, map_inv] using hu1
  · apply ψ.injective
    simpa [map_mul, map_inv] using hu2

end CFSG.RankThree.PartOne.Q1327C
