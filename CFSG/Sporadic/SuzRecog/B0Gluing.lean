module

public import CFSG.Sporadic.SuzRecog.B0GluingTwist
public import CFSG.Sporadic.SuzRecog.B0GluingNorm
public import CFSG.Sporadic.SuzRecog.B0GluingTau
public import CFSG.Sporadic.SuzRecog.LocalRLeafW0
public import CFSG.Blueprint.OddStandardExact
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34
public import CFSG.LocalAnalysis.OddStandard.Seitz77Thompson
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveRho
public import CFSG.Permutation.AlternatingAutomorphism

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.B0Gluing

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.ComponentClassification.AS81
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model


theorem suzB0Gluing : SuzB0Gluing := by
  intro G _ _ _ S hS hσ
  obtain ⟨hw, -, hΩ, hNWC, hL34⟩ := hS
  obtain ⟨σ₀⟩ := hσ
  obtain ⟨A, R, L⟩ := LocalR.exists_suzLocalR_leaf_w0 S hw hΩ hNWC σ₀ hL34
  obtain ⟨σ, hTA, hCA, hR0⟩ := exists_sigma_normal L
  obtain ⟨κ⟩ := L.equivS
  let φ : ↥(invE 1) →* G := S.M.subtype.comp σ.symm.toMonoidHom
  let ι : ↥J0 →* G := A.subtype.comp (κ.symm.toMonoidHom.comp j0Equiv.toMonoidHom)
  have hφ : Function.Injective φ := S.M.subtype_injective.comp σ.symm.injective
  have hι : Function.Injective ι :=
    A.subtype_injective.comp (κ.symm.injective.comp j0Equiv.injective)
  have hιA : ∀ x, ι x ∈ A := fun x => (κ.symm (j0Equiv x)).2
  have hιrange : ι.range = A := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact hιA x
    · intro hg
      refine ⟨j0Equiv.symm (κ ⟨g, hg⟩), ?_⟩
      show ((κ.symm (j0Equiv (j0Equiv.symm (κ ⟨g, hg⟩))) : ↥A) : G) = g
      rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  have hT : ∀ y (hy : y ∈ T0), φ ⟨y, T0_le_invE hy⟩ ∈ ι.range := fun y hy => by
    rw [hιrange]
    exact hTA y hy
  have hφA : ∀ y (hy : y ∈ A40), φ ⟨y, A40_le_invE hy⟩ ∈ centralizer (A : Set G) := hCA
  have hR : ∀ y (hy : y ∈ Model.R0) (x : ↥J0),
      φ ⟨y, R0_le_invE hy⟩ * ι x = ι x * φ ⟨y, R0_le_invE hy⟩ := fun y hy x =>
    (mem_centralizer_iff.mp (hφA y (R0_le_A40 hy)) _ (hιA x)).symm
  have hz1 : φ ⟨suzInv 1, SuzB0.suzInv_mem_invE⟩ = S.z := by
    have h := LocalR.map_zM S σ
    have e : σ.symm LocalR.t1Elt = S.zM := by rw [← h, MulEquiv.symm_apply_apply]
    show ((σ.symm LocalR.t1Elt : S.M) : G) = S.z
    rw [e]
    rfl
  have hz : ∀ g : G, g * φ ⟨suzInv 1, SuzB0.suzInv_mem_invE⟩ =
      φ ⟨suzInv 1, SuzB0.suzInv_mem_invE⟩ * g → g ∈ φ.range := fun g hg => by
    rw [hz1] at hg
    have hgM : g ∈ S.M := mem_centralizer_singleton_iff.mpr hg
    refine ⟨σ ⟨g, hgM⟩, ?_⟩
    show ((σ.symm (σ ⟨g, hgM⟩) : S.M) : G) = g
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨ι', hι'inj, hι'range, hι'T⟩ := exists_chart φ hφ ι hι hT hR hz
  let τ' : G := φ ⟨tau0, tau0_mem_invE⟩
  have hτ2 : τ' * τ' = 1 := by
    show φ _ * φ _ = 1
    rw [← map_mul]
    have e : (⟨tau0, tau0_mem_invE⟩ * ⟨tau0, tau0_mem_invE⟩ : ↥(invE 1)) = 1 :=
      Subtype.ext tau0_mul_self
    rw [e, map_one]
  have hτM : τ' ∈ S.M := (σ.symm ⟨tau0, tau0_mem_invE⟩).2
  have hστ : σ ⟨τ', hτM⟩ = ⟨tau0, tau0_mem_invE⟩ := by
    show σ (σ.symm ⟨tau0, tau0_mem_invE⟩) = _
    rw [MulEquiv.apply_symm_apply]
  have hτR : τ' ∈ normalizer (R : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
    have hxM : x ∈ S.M := L.comp.R_le_M hx
    have hcM : τ' * x * τ'⁻¹ ∈ S.M := mul_mem (mul_mem hτM hxM) (inv_mem hτM)
    refine (hR0 _ hcM).mp ?_
    have e : (⟨τ' * x * τ'⁻¹, hcM⟩ : S.M) = ⟨τ', hτM⟩ * ⟨x, hxM⟩ * ⟨τ', hτM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hστ]
    show tau0 * ((σ ⟨x, hxM⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * tau0⁻¹ ∈ Model.R0
    exact (mem_normalizer_iff.mp tau0_mem_B0.2 _).mp ((hR0 x hxM).mpr hx)
  have hτA : τ' ∈ normalizer (A : Set G) := by
    rw [← L.normalizer_eq]
    exact hτR
  have hnorm : ∀ x : ↥J0, ∃ y : ↥J0, τ' * ι' x * τ'⁻¹ = ι' y := fun x => by
    have h1 : ι' x ∈ A := by rw [← hιrange, ← hι'range]; exact ⟨x, rfl⟩
    have h2 : τ' * ι' x * τ'⁻¹ ∈ ι'.range := by
      rw [hι'range, hιrange]
      exact (mem_normalizer_iff.mp hτA _).mp h1
    obtain ⟨y, hy⟩ := h2
    exact ⟨y, hy.symm⟩
  have hTτ : ∀ x (hx : x ∈ T0) (hx' : tau0 * x * tau0⁻¹ ∈ J0),
      ι' ⟨_, hx'⟩ = τ' * ι' ⟨x, T0_le_J0 hx⟩ * τ'⁻¹ := fun x hx hx' => by
    have hx1 : x ∈ invE 1 := T0_le_invE hx
    have hT' : tau0 * x * tau0⁻¹ ∈ T0 := mem_inf.mpr ⟨hx',
      mul_mem (mul_mem tau0_mem_invE hx1) (inv_mem tau0_mem_invE)⟩
    rw [hι'T _ hT', hι'T x hx]
    have e : (⟨tau0 * x * tau0⁻¹, T0_le_invE hT'⟩ : ↥(invE 1)) =
        ⟨tau0, tau0_mem_invE⟩ * ⟨x, hx1⟩ * ⟨tau0, tau0_mem_invE⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  obtain ⟨α, hαT, hαrange, hατ⟩ := exists_tau_compat ι' hι'inj τ' hτ2 hnorm hTτ z2 z2_mem_T0
    (fun x hx => z2_comm hx) z2_mul_self tau0_conj_z2 suzInv_one_not_comm_zJ0
    (fun g hg hc => centR_T0 hg hc)
  let β : ↥A40 →* G := φ.comp (inclusion A40_le_invE)
  have hcomm : ∀ j : ↥J0, ∀ a : ↥A40, α j * β a = β a * α j := fun j a => by
    obtain ⟨y, hy⟩ := hαrange j
    have h1 : α j ∈ A := by rw [hy, ← hιrange, ← hι'range]; exact ⟨y, rfl⟩
    exact mem_centralizer_iff.mp (hφA a.1 a.2) _ h1
  have hτβ : ∀ x (hx : x ∈ A40) (hx' : tau0 * x * tau0⁻¹ ∈ A40),
      β ⟨_, hx'⟩ = τ' * β ⟨x, hx⟩ * τ'⁻¹ := fun x hx hx' => by
    have e : (inclusion A40_le_invE ⟨_, hx'⟩ : ↥(invE 1)) =
        ⟨tau0, tau0_mem_invE⟩ * inclusion A40_le_invE ⟨x, hx⟩ * ⟨tau0, tau0_mem_invE⟩⁻¹ := rfl
    show φ _ = φ _ * φ _ * (φ _)⁻¹
    rw [e, map_mul, map_mul, map_inv]
  obtain ⟨ψ, hψJ, hψA, hψτ⟩ := exists_hom_NR0 α β τ' hcomm hτ2 hατ hτβ
  refine ⟨σ, ψ, b0Agree_of σ ψ (fun i hi h1 h2 => ?_) (fun h1 h2 => ?_) (fun h1 h2 => ?_)
    (fun h1 h2 => ?_)⟩
  · rw [hψJ _ (t0Gen_mem_J0 hi), hαT _ (t0Gen_mem_T0 hi), hι'T _ (t0Gen_mem_T0 hi)]
    rfl
  · rw [hψA _ w0_mem_A40]
    rfl
  · rw [hψA _ rho1_mem_A40]
    rfl
  · rw [hψτ]
    rfl

end CFSG.Sporadic.SuzRecog.B0Gluing
