module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectSUDiag
public import CFSG.LocalAnalysis.StandardType.GGHypSix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import CFSG.LieType.Universal.Unitary.Clause0
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
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank Matrix
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr rootDatum)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

namespace RootDetectSU

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}

omit [Finite F] [CharP F 2] in
theorem unitaryFieldData_two (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    UnitaryFieldData 2 f F :=
  ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩

theorem bar_eq (h : UnitaryFieldData 2 f F) (c : F) : h.bar c = unitaryInvolution F 2 f c := by
  rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]

theorem map_eq_map_bar (h : UnitaryFieldData 2 f F) (M : Matrix (Fin n) (Fin n) F) :
    M.map (unitaryInvolution F 2 f) = M.map h.bar := by
  ext i j
  rw [map_apply, map_apply, bar_eq]

theorem SU_eq_gramSU_antidiag (h : UnitaryFieldData 2 f F) :
    SU (unitaryInvolution F 2 f) n = gramSU h (antidiag n : Matrix (Fin n) (Fin n) F) := by
  ext g
  rw [CFSG.LieType.Universal.Unitary.mem_SU, mem_gramSU, conjTr, map_eq_map_bar h]
  exact and_comm

omit [Finite F] [CharP F 2] in
theorem isPrimeFormGram_of_eq_antidiag {C : GL (Fin n) F}
    (hC : (C : Matrix (Fin n) (Fin n) F) = antidiag n) : IsPrimeFormGram C where
  symm := by
    rw [hC]
    ext i j
    simp only [transpose_apply, antidiag, of_apply]
    by_cases hij : i = Fin.rev j
    · rw [ite_eq_left hij, ite_eq_left (by rw [hij, Fin.rev_rev])]
    · rw [ite_eq_right hij, ite_eq_right (fun h' => hij (by rw [h', Fin.rev_rev]))]
  prime := by
    intro i j
    rw [hC]
    simp only [antidiag, of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem exists_div_eq (h : UnitaryFieldData 2 f F) {u : F}
    (hu : u * unitaryInvolution F 2 f u = 1) :
    ∃ ρ : F, ρ ≠ 0 ∧ ρ / unitaryInvolution F 2 f ρ = u := by
  obtain ⟨ρ, hρ0, hρ⟩ := h.exists_div_bar_eq (u := u)
    (by rw [UnitaryFieldData.norm, bar_eq h, hu])
  exact ⟨ρ, hρ0, by rw [← bar_eq h, hρ]⟩

theorem diagGL_mem_primeFormUnitary (h : UnitaryFieldData 2 f F)
    {t : Fin n → F} (ht : ∀ a, unitaryInvolution F 2 f (t a) * t (Fin.rev a) = 1) :
    diagGL t (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary ht) ∈
      primeFormUnitary h (antidiag n : Matrix (Fin n) (Fin n) F) := by
  rw [mem_primeFormUnitary, coe_diagGL, ← map_eq_map_bar h]
  exact conjTr_diagonal_mul t ht

theorem ggPsiInnerDiag_su (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 4 ≤ n)
    {G : Type*} [Group G] {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) {p : ℕ} (hp : Odd p)
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ (rootDatum hF n).roots) {u : SU (unitaryInvolution F 2 f) n}
    (hT : GGTorusOnRoot (rootDatum hF n) ψ c γ u) :
    GGPsiInnerDiag (rootDatum hF n) ψ c := by
  classical
  have hσ : ∀ x, unitaryInvolution F 2 f (unitaryInvolution F 2 f x) = x :=
    unitaryInvolution_involutive hF
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have h : UnitaryFieldData 2 f F := unitaryFieldData_two hF hf
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : GL (Fin n) F, (C₀ : Matrix (Fin n) (Fin n) F) = antidiag n :=
    ⟨⟨antidiag n, antidiag n, CFSG.LieType.Universal.Unitary.antidiag_mul_self n,
      CFSG.LieType.Universal.Unitary.antidiag_mul_self n⟩, rfl⟩
  have hC : IsPrimeFormGram C₀ := isPrimeFormGram_of_eq_antidiag hC₀
  set C : Matrix (Fin n) (Fin n) F := (C₀ : Matrix (Fin n) (Fin n) F) with hCdef
  have hE : SU (unitaryInvolution F 2 f) n = gramSU h C := by
    show SU (unitaryInvolution F 2 f) n = gramSU h C
    rw [hC₀]
    exact SU_eq_gramSU_antidiag h
  set E : SU (unitaryInvolution F 2 f) n ≃* gramSU h C := MulEquiv.subgroupCongr hE with hEdef
  set ψ' : gramSU h C →* G := ψ.comp E.symm.toMonoidHom with hψ'def
  have hψ'E : ∀ y, ψ' (E y) = ψ y := fun y => by
    rw [hψ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  have hrange : ψ'.range = ψ.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨E.symm y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨E y, hψ'E y⟩
  have hker' : ψ'.ker ≤ Subgroup.center (gramSU h C) := by
    intro y hy
    have hz : E.symm y ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n) := hker hy
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have e := congrArg E (hz (E.symm g))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at e
  have hperf : ⁅(⊤ : Subgroup (gramSU h C)), (⊤ : Subgroup (gramSU h C))⁆ = ⊤ := by
    have := (CFSG.LieType.Universal.Unitary.isQuasisimple_SU hF hn3
      (fun h' => hq ⟨(Prod.mk.inj h').1, (Prod.mk.inj h').2⟩)).1
    have : Group.IsPerfect (gramSU h C) :=
      Group.IsPerfect.ofSurjective (f := E.toMonoidHom) E.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hN : normOneScalars h (gramSU h C) n = Subgroup.center (gramSU h C) :=
    (CFSG.SeitzReduction.F4Pilot.center_gramSU_eq_normOneScalars h hC hn3 hq).symm
  rw [← hrange] at hc hcp
  obtain ⟨α, hα⟩ := RootDetect.exists_quotAut hN hperf hker' hc
  have hαp : α ^ p = 1 := RootDetect.quotAut_pow_eq_one hN.ge hker' hc hα hcp
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn3 hq α
  have hφp : φ ^ p = 1 := by
    have e1 := primeFormFieldFactor_psi h hC hn3 hq ⟨A, φ⟩
    rw [hAφ] at e1
    change primeFormFieldFactor h hC hn3 hq α = φ at e1
    rw [← e1, ← map_pow, hαp, map_one]
  rw [primeFormPsi_apply] at hAφ
  obtain ⟨W, hW⟩ := RootDetect.exists_conj_of_torusOnRoot _ hT
  obtain ⟨Em, hEm0, hEmap, helt⟩ := exists_rootElt hσ hγ
  have hfix : ∀ t, unitaryInvolution F 2 f t = t → φ t = t := by
    set N : GL (Fin n) F := ((W : GL (Fin n) F))⁻¹ * (A : GL (Fin n) F) *
      glAut φ (u : GL (Fin n) F) with hNdef
    refine fixed_of_mul_conj (T := {t | unitaryInvolution F 2 f t = t}) hEm0
      (M := (N : Matrix (Fin n) (Fin n) F))
      (M' := ((N⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) (map_one _) ?_
    intro t ht
    obtain ⟨x, hx, hxm, hxx⟩ := helt t ht
    have h1 := hα (E (u * x * u⁻¹)) (E (W * x * W⁻¹)) (by rw [hψ'E, hψ'E]; exact hW x hx)
    rw [← hAφ, MulAut.mul_apply] at h1
    change primeFormConjAut h C A (primeFormFieldAut h hC φ _) = _ at h1
    rw [primeFormFieldAut_mk, primeFormConjAut_mk] at h1
    obtain ⟨c0, -, -, hc0⟩ := QuotientGroup.eq.mp h1
    set v : GL (Fin n) F := ((u * x * u⁻¹ : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F)
      with hv
    set M : GL (Fin n) F := (A : GL (Fin n) F) * glAut φ v * (A : GL (Fin n) F)⁻¹ with hM
    set M' : GL (Fin n) F := ((W * x * W⁻¹ : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F)
      with hM'
    have hc0' : M⁻¹ * M' = GeneralLinearGroup.scalar (Fin n) c0 := hc0
    have hsq1 : ∀ y : SU (unitaryInvolution F 2 f) n, (y * x * y⁻¹) * (y * x * y⁻¹) = 1 :=
      fun y => by
        calc (y * x * y⁻¹) * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
          _ = 1 := by rw [hxx, mul_one, mul_inv_cancel]
    have hvv : v * v = 1 := by rw [hv, ← Subgroup.coe_mul, hsq1, Subgroup.coe_one]
    have hMM : M * M = 1 := by
      calc M * M = (A : GL (Fin n) F) * (glAut φ v * glAut φ v) * (A : GL (Fin n) F)⁻¹ := by
            rw [hM]; group
        _ = 1 := by rw [← map_mul, hvv, map_one, mul_one, mul_inv_cancel]
    have hM'M' : M' * M' = 1 := by rw [hM', ← Subgroup.coe_mul, hsq1, Subgroup.coe_one]
    have heq := eq_of_inv_mul_eq_scalar hc0' hMM hM'M'
    have e : (W : GL (Fin n) F) * (x : GL (Fin n) F) * (W : GL (Fin n) F)⁻¹ =
        (A : GL (Fin n) F) * (glAut φ (u : GL (Fin n) F) * glAut φ (x : GL (Fin n) F) *
          (glAut φ (u : GL (Fin n) F))⁻¹) * (A : GL (Fin n) F)⁻¹ := by
      have e2 := heq
      rw [hM', hM, hv] at e2
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using e2
    have e4 : (x : GL (Fin n) F) * N = N * glAut φ (x : GL (Fin n) F) :=
      HypSixTypeA.mul_conj_rel e
    have e3 := congrArg Units.val e4
    rw [Units.val_mul (x : GL (Fin n) F) N, Units.val_mul N, coe_glAut, hxm,
      Matrix.map_add _ (map_add φ),
      Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_smul' _ _ _ (map_mul φ),
      hEmap] at e3
    exact e3
  have hcomm : ∀ x, φ (unitaryInvolution F 2 f x) = unitaryInvolution F 2 f (φ x) := fun x => by
    rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]
  have hφ1 : φ = 1 := eq_one_of_fixed_of_pow_eq_one hσ hcomm hfix hp hφp
  rw [hφ1, map_one, mul_one] at hAφ
  have hsqrt : ∀ x : F, ∃ y, y * y = x := fun x => by
    obtain ⟨y, hy⟩ := isSquare_of_charTwo' x
    exact ⟨y, hy.symm⟩
  have h90 : ∀ w : F, w * unitaryInvolution F 2 f w = 1 →
      ∃ ρ : F, ρ ≠ 0 ∧ ρ / unitaryInvolution F 2 f ρ = w := fun w hw => exists_div_eq h hw
  set ν₀ : F := ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det with hν₀
  have hν : ν₀ * unitaryInvolution F 2 f ν₀ = 1 := by
    have e := norm_det_eq_one h C₀ A.2
    rwa [UnitaryFieldData.norm, bar_eq h] at e
  have hν0 : ν₀ ≠ 0 := left_ne_zero_of_mul_eq_one hν
  obtain ⟨δ, hδ0, hδ⟩ := h90 ν₀ hν
  set b : Fin n := ⟨0, by omega⟩ with hbdef
  have hb : b ≠ Fin.rev b := Fin.ne_of_val_ne (by simp [b]; omega)
  have hdu := pairDiag_unitary hσ hb hδ0
  set dGL : GL (Fin n) F := diagGL (pairDiag (unitaryInvolution F 2 f) b δ)
    (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary hdu) with hdGL
  have hdU : dGL ∈ primeFormUnitary h C := by
    show dGL ∈ primeFormUnitary h C
    rw [hC₀]
    exact diagGL_mem_primeFormUnitary h hdu
  have hddet : ((dGL : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = ν₀ := by
    rw [hdGL, coe_diagGL, det_diagonal, prod_pairDiag hb, ← div_eq_mul_inv, hδ]
  set a : GL (Fin n) F := (A : GL (Fin n) F) * dGL⁻¹ with hadef
  have ha : a ∈ gramSU h C := by
    refine (mem_gramSU_iff_unitary h).mpr ⟨mul_mem A.2 (inv_mem hdU), ?_⟩
    have e : ((a * dGL : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = ν₀ := by
      rw [hadef, inv_mul_cancel_right]
    rw [Units.val_mul, det_mul, hddet] at e
    exact mul_right_cancel₀ hν0 (e.trans (one_mul ν₀).symm)
  set β : gramSU h C →* gramSU h C := (primeFormConjSU h C ⟨dGL, hdU⟩).toMonoidHom with hβ
  have haα : ∀ y : gramSU h C, α (y : primeFormP h C) =
      ((⟨a, ha⟩ * β y * (⟨a, ha⟩ : gramSU h C)⁻¹ : gramSU h C) : primeFormP h C) := by
    intro y
    rw [← hAφ, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (A : GL (Fin n) F) * y * (A : GL (Fin n) F)⁻¹ = a * (dGL * y * dGL⁻¹) * a⁻¹
    rw [hadef]
    group
  have hlift := conj_eq_of_quotAut_eq hN hperf hc hα haα
  refine ⟨ψ' ⟨a, ha⟩, ⟨E.symm ⟨a, ha⟩, rfl⟩, fun γ' hγ' => ?_⟩
  have hνi : ν₀⁻¹ * unitaryInvolution F 2 f ν₀⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hν, inv_one]
  obtain ⟨r, hru, hrprod, hrconst⟩ := exists_unitaryDiag_of_mem_roots hσ hsqrt h90 hn hγ' hνi
  have htu := unitary_mul hdu hru
  have htdet : ∏ x, (pairDiag (unitaryInvolution F 2 f) b δ * r) x = 1 := by
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib, prod_pairDiag hb, ← div_eq_mul_inv, hδ, hrprod,
      mul_inv_cancel₀ hν0]
  set hel := diagSU (unitaryInvolution F 2 f) _ htu htdet with hheldef
  have hmem : hel ∈ ggTorus (rootDatum hF n) := by
    simp only [ggTorus, Subgroup.mem_iInf]
    intro γ'' _
    exact mem_normalizer_rootGroup_of_mem_diagSubgroup hσ
      (diagSU_mem_diagSubgroup _ htu htdet) γ''
  refine ⟨hel, hmem, fun z hz => ?_⟩
  set rGL : GL (Fin n) F := diagGL r (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary hru)
    with hrGL
  have hcommr : rGL * (z : GL (Fin n) F) = (z : GL (Fin n) F) * rGL := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hrGL, coe_diagGL]
    exact diagonal_mul_comm_of_mem_rootGroup hσ hrconst hz)
  have hhel : ((hel : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F) = dGL * rGL :=
    Units.ext (by
      rw [Units.val_mul, hheldef, coe_diagSU, coe_diagGL, hdGL, hrGL, coe_diagGL, coe_diagGL,
        diagonal_mul_diagonal]
      rfl)
  have key : ((hel * z * hel⁻¹ : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F) =
      dGL * (z : GL (Fin n) F) * dGL⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hhel, mul_assoc dGL rGL, hcommr]
    group
  rw [← hψ'E z, hlift (E z), ← hψ'E (hel * z * hel⁻¹)]
  congr 1
  apply Subtype.ext
  change dGL * (z : GL (Fin n) F) * dGL⁻¹ =
    ((hel * z * hel⁻¹ : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F)
  rw [key]

end RootDetectSU

section Family

theorem ggRootDetect_psu : GGRootDetect .PSU := by
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have e : ggU .PSU n f =
        ⟨SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e]
    intro ψ _ hrk hker p hp hp2 _ c hc hcp γ hγ u hT
    have hrk' : 2 ≤ n / 2 := hrk
    exact RootDetectSU.ggPsiInnerDiag_su (card_galoisField_two_mul 2 f hf) hf (by omega) hker
      (hp.odd_of_ne_two hp2) hc hcp hγ hT
  · intro ψ hadm
    exact absurd hadm.2.1 hf

end Family

end CFSG.StandardType
