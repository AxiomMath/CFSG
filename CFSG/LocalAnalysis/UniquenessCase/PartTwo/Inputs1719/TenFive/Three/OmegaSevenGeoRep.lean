module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenGeoDefs
import CFSG.ClassicalInvolution.ModelFacts.OrthAutSim
import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1Iso

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Open QuadraticMap
  CFSG.ComponentClassification.CatalogueBHigherLinearField

private theorem omSevenGR_card_idx : Fintype.card OmegaSevenIdx = 7 := by
  simp [OmegaSevenIdx, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

private theorem omSevenGR_ringEquiv_eq_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (φ : K ≃+* K) : φ = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardF : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hcard : Fintype.card K = Fintype.card (ZMod 3) := by rw [hcardF, ZMod.card]
  let e : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  have hψ : e.symm.trans (φ.trans e) = 1 := Subsingleton.elim _ _
  apply RingEquiv.ext
  intro x
  have h := congrArg (fun g : ZMod 3 ≃+* ZMod 3 => g (e x)) hψ
  simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply, RingEquiv.refl_apply] at h
  exact e.injective h

private theorem omSevenGR_det_conj {K : Type} [Field K]
    (B x : Matrix.GeneralLinearGroup OmegaSevenIdx K) :
    Matrix.det ((B * x * B⁻¹ : Matrix.GeneralLinearGroup OmegaSevenIdx K) :
        Matrix OmegaSevenIdx OmegaSevenIdx K) =
      Matrix.det (x : Matrix OmegaSevenIdx OmegaSevenIdx K) := by
  have h := Matrix.det_units_conj (B : (Matrix OmegaSevenIdx OmegaSevenIdx K)ˣ)
    (x : Matrix OmegaSevenIdx OmegaSevenIdx K)
  simpa using h

private theorem omSevenGR_two_ne_zero {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    (2 : K) ≠ 0 := by
  letI : Fintype K := Fintype.ofFinite K
  intro hc
  have hdvd : ringChar K ∣ 2 := ringChar.dvd hc
  have hc2 : ringChar K = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  have heven := FiniteField.even_card_of_char_two (F := K) hc2
  rw [Fintype.card_eq_nat_card, hK] at heven
  norm_num at heven

theorem exists_isometry_of_involution {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (σ : MulAut (StatedProj (StatedOmega (StatedQuadOdd 3 K)))) (hσ : orderOf σ = 2) :
    ∃ A : Matrix.GeneralLinearGroup OmegaSevenIdx K,
      (∀ v, quadOdd 3 K (A.val.mulVec v) = quadOdd 3 K v) ∧ A * A = 1 ∧
      A ∉ StatedScalars OmegaSevenIdx K ∧
      ∀ x : StatedOmega (StatedQuadOdd 3 K), ∃ y : StatedOmega (StatedQuadOdd 3 K),
        (y : Matrix.GeneralLinearGroup OmegaSevenIdx K) =
            A * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) * A⁻¹ ∧
          σ (QuotientGroup.mk x) = QuotientGroup.mk y := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h2 : (2 : K) ≠ 0 := omSevenGR_two_ne_zero hK
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  obtain ⟨A, φ, μ, hQ, hσA⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_similarity_odd hadm (by simpa using hK) σ
  have hφ : φ = 1 := omSevenGR_ringEquiv_eq_one hK φ
  have hglφ : glFieldEquiv (K := K) (F := K) OmegaSevenIdx φ = 1 := by
    rw [hφ]; rfl
  have hQ1 : ∀ v : OmegaSevenIdx → K, quadOdd 3 K (A.val.mulVec v) = μ * quadOdd 3 K v := by
    intro v
    have h := hQ v
    rw [hφ] at h
    simpa using h
  have hnd : (polarBilin (quadOdd 3 K)).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd 3 K h2
  have hdetrel : A.val.det ^ 2 = (μ : K) ^ Fintype.card OmegaSevenIdx :=
    CFSG.ComponentClassification.HarrisLit.T1.det_sq_eq_pow_card_of_similitude
      (quadOdd 3 K) hnd A.val (μ : K) hQ1
  have hdet0 : A.val.det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hdet3 : A.val.det ^ 3 = A.val.det := by
    have h := FiniteField.pow_card (A.val.det)
    rwa [hcardF] at h
  have hdet_sq : A.val.det ^ 2 = 1 := by
    have h3 : A.val.det * A.val.det ^ 2 = A.val.det * 1 := by
      rw [mul_one]
      calc A.val.det * A.val.det ^ 2 = A.val.det ^ 3 := by ring
        _ = A.val.det := hdet3
    exact mul_left_cancel₀ hdet0 h3
  have hμ7 : (μ : K) ^ 7 = 1 := by
    have h := hdetrel
    rw [hdet_sq, omSevenGR_card_idx] at h
    exact h.symm
  have hμ3 : (μ : K) ^ 3 = (μ : K) := by
    have h := FiniteField.pow_card (μ : K)
    rwa [hcardF] at h
  have hμ : (μ : K) = 1 := by
    have h7 : (μ : K) ^ 7 = (μ : K) := by
      calc (μ : K) ^ 7 = (μ : K) ^ 3 * (μ : K) ^ 3 * (μ : K) := by ring
        _ = (μ : K) * (μ : K) * (μ : K) := by rw [hμ3]
        _ = (μ : K) ^ 3 := by ring
        _ = (μ : K) := hμ3
    rw [← h7]; exact hμ7
  have hAiso : ∀ v, quadOdd 3 K (A.val.mulVec v) = quadOdd 3 K v := by
    intro v; rw [hQ1 v, hμ, one_mul]
  have hσA' : ∀ x : StatedOmega (StatedQuadOdd 3 K),
      ∃ y : StatedOmega (StatedQuadOdd 3 K),
        (y : Matrix.GeneralLinearGroup OmegaSevenIdx K) =
            A * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) * A⁻¹ ∧
          σ (QuotientGroup.mk x) = QuotientGroup.mk y := by
    intro x
    obtain ⟨y, hy, hσy⟩ := hσA x
    refine ⟨y, ?_, hσy⟩
    rw [hglφ] at hy
    simpa using hy
  have hσ2 : σ * σ = 1 := by
    rw [← pow_two, ← hσ]
    exact pow_orderOf_eq_one σ
  have hcommA : ∀ x : StatedOmega (StatedQuadOdd 3 K),
      (A * A) * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) * (A * A)⁻¹ =
        (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) := by
    intro x
    obtain ⟨y, hy, hσy⟩ := hσA' x
    obtain ⟨z, hz, hσz⟩ := hσA' y
    have hzy : (QuotientGroup.mk z : StatedProj (StatedOmega (StatedQuadOdd 3 K))) =
        QuotientGroup.mk x := by
      have h1 : σ (σ (QuotientGroup.mk x)) = QuotientGroup.mk x := by
        rw [show σ (σ (QuotientGroup.mk x)) = (σ * σ) (QuotientGroup.mk x) from rfl,
          hσ2, MulAut.one_apply]
      rw [← hσz, ← hσy]
      exact h1
    have hzB : (z : Matrix.GeneralLinearGroup OmegaSevenIdx K) =
        (A * A) * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) * (A * A)⁻¹ := by
      rw [hz, hy]; group
    have hmem : (A * A) * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) * (A * A)⁻¹ ∈
        StatedOmega (StatedQuadOdd 3 K) := by
      rw [← hzB]; exact z.2
    have hwmk : (QuotientGroup.mk (⟨(A * A) * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) *
        (A * A)⁻¹, hmem⟩ : StatedOmega (StatedQuadOdd 3 K)) :
          StatedProj (StatedOmega (StatedQuadOdd 3 K))) = QuotientGroup.mk x := by
      have : (⟨(A * A) * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) * (A * A)⁻¹, hmem⟩ :
          StatedOmega (StatedQuadOdd 3 K)) = z := Subtype.ext hzB.symm
      rw [this]; exact hzy
    obtain ⟨u, hu⟩ := (CFSG.Open.StatedAPI.statedProj_mk_eq_iff (StatedOmega (StatedQuadOdd 3 K))
      ⟨(A * A) * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) * (A * A)⁻¹, hmem⟩ x).mp hwmk
    have hdetx0 : Matrix.det ((x : Matrix.GeneralLinearGroup OmegaSevenIdx K) :
        Matrix OmegaSevenIdx OmegaSevenIdx K) ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    have hu7 : (u : K) ^ 7 = 1 := by
      have h := congrArg Matrix.det hu
      rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, omSevenGR_card_idx] at h
      have ha : Matrix.det (((⟨(A * A) * (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) *
          (A * A)⁻¹, hmem⟩ : StatedOmega (StatedQuadOdd 3 K)) :
            Matrix.GeneralLinearGroup OmegaSevenIdx K) : Matrix OmegaSevenIdx OmegaSevenIdx K) =
          Matrix.det ((x : Matrix.GeneralLinearGroup OmegaSevenIdx K) :
            Matrix OmegaSevenIdx OmegaSevenIdx K) :=
        omSevenGR_det_conj (A * A) (x : Matrix.GeneralLinearGroup OmegaSevenIdx K)
      rw [ha] at h
      have h' : Matrix.det ((x : Matrix.GeneralLinearGroup OmegaSevenIdx K) :
          Matrix OmegaSevenIdx OmegaSevenIdx K) * 1 =
          Matrix.det ((x : Matrix.GeneralLinearGroup OmegaSevenIdx K) :
            Matrix OmegaSevenIdx OmegaSevenIdx K) * (u : K) ^ 7 := by
        rw [mul_one]; exact h
      exact (mul_left_cancel₀ hdetx0 h').symm
    have hu1 : u = 1 := by
      apply Units.ext
      have hu3 : (u : K) ^ 3 = (u : K) := by
        have h := FiniteField.pow_card (u : K)
        rwa [hcardF] at h
      have h7 : (u : K) ^ 7 = (u : K) := by
        calc (u : K) ^ 7 = (u : K) ^ 3 * (u : K) ^ 3 * (u : K) := by ring
          _ = (u : K) * (u : K) * (u : K) := by rw [hu3]
          _ = (u : K) ^ 3 := by ring
          _ = (u : K) := hu3
      rw [← h7]; exact hu7
    rw [hu1] at hu
    simp only [Units.val_one, one_smul, mul_one] at hu
    exact Units.ext hu.symm
  have hfin : Module.finrank K (OmegaSevenIdx → K) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, omSevenGR_card_idx]
  have hW3 : 3 ≤ Module.finrank K (OmegaSevenIdx → K) := by rw [hfin]; norm_num
  let B : Matrix.GeneralLinearGroup OmegaSevenIdx K := A * A
  let L : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K) := toLinEquiv OmegaSevenIdx K B
  let M : (OmegaSevenIdx → K) →ₗ[K] (OmegaSevenIdx → K) := L.toLinearMap
  have hcentral :=
    CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar
      (K := K) (W := OmegaSevenIdx → K) (by rw [hK]; norm_num) (quadOdd 3 K) hnd hW3
  have hcomm : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K)⁆,
      M ∘ₗ (g : (OmegaSevenIdx → K) →ₗ[K] (OmegaSevenIdx → K)) =
        (g : (OmegaSevenIdx → K) →ₗ[K] (OmegaSevenIdx → K)) ∘ₗ M := by
    intro g hg
    have hgΩ : (toLinEquiv OmegaSevenIdx K).symm g ∈ StatedOmega (StatedQuadOdd 3 K) := by
      rw [statedOmega_eq_comap (coe_quadOdd 3 K)]
      exact Subgroup.mem_comap.mpr (by simpa using hg)
    have hB := hcommA ⟨(toLinEquiv OmegaSevenIdx K).symm g, hgΩ⟩
    have hLg : L * g = g * L := by
      have h := congrArg (toLinEquiv OmegaSevenIdx K) hB
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h
      calc L * g = L * g * L⁻¹ * L := by group
        _ = g * L := by rw [h]
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun e : (OmegaSevenIdx → K) ≃ₗ[K] (OmegaSevenIdx → K) => e v) hLg
    simpa [M, L, LinearEquiv.mul_apply, LinearMap.comp_apply] using hv
  obtain ⟨c, hc⟩ := (hcentral.1 M).mp hcomm
  have hc0 : c ≠ 0 := by
    intro hc0
    have hM0 : M = 0 := by rw [hc, hc0, zero_smul]
    have h1 : M (1 : OmegaSevenIdx → K) = 0 := by rw [hM0]; rfl
    have h2 : (1 : OmegaSevenIdx → K) = 0 := L.injective (by simpa [M] using h1)
    exact one_ne_zero h2
  let u : Kˣ := Units.mk0 c hc0
  have hBscalar : B = Matrix.GeneralLinearGroup.scalar OmegaSevenIdx u := by
    apply (toLinEquiv OmegaSevenIdx K).injective
    change L = toLinEquiv OmegaSevenIdx K (Matrix.GeneralLinearGroup.scalar OmegaSevenIdx u)
    apply LinearEquiv.ext
    intro v
    have hv := congrArg (fun f : (OmegaSevenIdx → K) →ₗ[K] (OmegaSevenIdx → K) => f v) hc
    have h2 : (toLinEquiv OmegaSevenIdx K (Matrix.GeneralLinearGroup.scalar OmegaSevenIdx u)) v =
        c • v := by
      simp [Matrix.GeneralLinearGroup.coe_scalar, u]
    rw [h2]
    exact hv
  have hu1 : u = 1 := by
    apply Units.ext
    have hu_eq : u = Matrix.GeneralLinearGroup.det A ^ 2 := by
      have hdetB : Matrix.GeneralLinearGroup.det B = u := by
        rw [hBscalar]
        have hu3 : (u : K) ^ 3 = (u : K) := by
          have h := FiniteField.pow_card (u : K)
          rwa [hcardF] at h
        have h7 : (u : K) ^ 7 = (u : K) := by
          calc (u : K) ^ 7 = (u : K) ^ 3 * (u : K) ^ 3 * (u : K) := by ring
            _ = (u : K) * (u : K) * (u : K) := by rw [hu3]
            _ = (u : K) ^ 3 := by ring
            _ = (u : K) := hu3
        rw [Matrix.GeneralLinearGroup.det_scalar, omSevenGR_card_idx]
        exact Units.ext h7
      have hdetA : Matrix.GeneralLinearGroup.det B = Matrix.GeneralLinearGroup.det A ^ 2 := by
        rw [show B = A * A from rfl, map_mul, pow_two]
      rw [hdetB] at hdetA
      exact hdetA
    rw [hu_eq, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, hdet_sq,
      Units.val_one]
  have hBsq : B = 1 := by rw [hBscalar, hu1, map_one]
  have hAnotScalar : A ∉ StatedScalars OmegaSevenIdx K := by
    intro hA
    obtain ⟨u, hu⟩ := hA
    have hσ1 : σ = 1 := by
      apply MulEquiv.ext
      intro p
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨y, hy, hσy⟩ := hσA' x
      rw [hσy]
      have hyx : (y : Matrix.GeneralLinearGroup OmegaSevenIdx K) =
          (x : Matrix.GeneralLinearGroup OmegaSevenIdx K) := by
        rw [hy, ← hu]
        rw [Matrix.GeneralLinearGroup.scalar_commute u
          (x : Matrix.GeneralLinearGroup OmegaSevenIdx K)]
        group
      rw [Subtype.ext hyx]
      rfl
    have h2' := hσ
    rw [hσ1, orderOf_one] at h2'
    norm_num at h2'
  exact ⟨A, hAiso, hBsq, hAnotScalar, hσA'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
