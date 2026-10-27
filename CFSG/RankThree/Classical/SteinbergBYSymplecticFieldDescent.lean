module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.RankThree.Classical.SemilinearFixedBasis
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis

public noncomputable section

namespace CFSG.RankThree.Classical.SteinbergBY

open Matrix

section Generic

theorem commutator_mem_of_forall_zpow_mul_mem {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (g : G) (h : ∀ x, ∃ k : ℤ, g ^ k * x ∈ N) (x y : G) : x * y * x⁻¹ * y⁻¹ ∈ N := by
  have hmk : ∀ z : G, ∃ k : ℤ, (z : G ⧸ N) = (g : G ⧸ N) ^ k := by
    intro z
    obtain ⟨a, ha⟩ := h z
    refine ⟨-a, ?_⟩
    have h1 : ((g ^ a * z : G) : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    rw [_root_.zpow_neg]
    exact eq_inv_of_mul_eq_one_right h1
  obtain ⟨a, ha⟩ := hmk x
  obtain ⟨b, hb⟩ := hmk y
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, ha, hb]
  group

theorem exists_transpose_mul_mul_eq_J {F : Type*} [Field F] {r : ℕ}
    (G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) (halt : ∀ v, v ⬝ᵥ G *ᵥ v = 0)
    (hdet : G.det ≠ 0) :
    ∃ P : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F,
      P.det ≠ 0 ∧ Pᵀ * G * P = Matrix.J (Fin r) F := by
  classical
  have hB : (Matrix.toBilin' G).IsAlt := fun v => by
    rw [Matrix.toBilin'_apply']
    exact halt v
  have hnd : (Matrix.toBilin' G).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  obtain ⟨m, b, hb⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J hB hnd
  have hm : m = r := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Module.finrank_fintype_fun_eq_card] at h1
    simp only [Fintype.card_sum, Fintype.card_fin] at h1
    omega
  subst hm
  refine ⟨(Pi.basisFun F (Fin m ⊕ Fin m)).toMatrix b, fun h0 => ?_, ?_⟩
  · have h := (Pi.basisFun F (Fin m ⊕ Fin m)).toMatrix_mul_toMatrix_flip b
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  · rw [← hb, ← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun F _) b,
      LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']

end Generic

section Powers

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv glFieldEquiv_scalar)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (conjAut_mul_fieldAut_eq_one_iff)

variable {r : ℕ} {K : Type} [Field K]

theorem gspFieldMap_mul (σ : K ≃+* K) (A B : gsp r K) :
    gspFieldMap σ (A * B) = gspFieldMap σ A * gspFieldMap σ B :=
  Subtype.ext (map_mul (glFieldEquiv (Fin r ⊕ Fin r) σ) _ _)

theorem gspFieldMap_gspFieldMap (σ τ : K ≃+* K) (A : gsp r K) :
    gspFieldMap σ (gspFieldMap τ A) = gspFieldMap (σ * τ) A := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

theorem gspFieldMap_one (A : gsp r K) : gspFieldMap 1 A = A := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

theorem gspFieldMap_one_right (σ : K ≃+* K) : gspFieldMap σ (1 : gsp r K) = 1 :=
  Subtype.ext (map_one (glFieldEquiv (Fin r ⊕ Fin r) σ))

@[expose] def gspTwistedNorm (σ : K ≃+* K) (A : gsp r K) : ℕ → gsp r K
  | 0 => 1
  | k + 1 => gspTwistedNorm σ A k * gspFieldMap (σ ^ k) A

theorem gspTwistedNorm_zero (σ : K ≃+* K) (A : gsp r K) : gspTwistedNorm σ A 0 = 1 := rfl

theorem gspTwistedNorm_succ (σ : K ≃+* K) (A : gsp r K) (k : ℕ) :
    gspTwistedNorm σ A (k + 1) = gspTwistedNorm σ A k * gspFieldMap (σ ^ k) A := rfl

theorem gspTwistedNorm_succ' (σ : K ≃+* K) (A : gsp r K) (k : ℕ) :
    gspTwistedNorm σ A (k + 1) = A * gspFieldMap σ (gspTwistedNorm σ A k) := by
  induction k with
  | zero =>
    rw [gspTwistedNorm_succ, gspTwistedNorm_zero, pow_zero, gspFieldMap_one, one_mul,
      gspFieldMap_one_right, mul_one]
  | succ k ih =>
    conv_rhs => rw [gspTwistedNorm_succ σ A k, gspFieldMap_mul, gspFieldMap_gspFieldMap,
      ← pow_succ']
    rw [gspTwistedNorm_succ σ A (k + 1), ih, mul_assoc]

theorem fieldAut_mul_conjAut (τ : K ≃+* K) (A : gsp r K) :
    fieldAut r K τ * conjAut r K A = conjAut r K (gspFieldMap τ A) * fieldAut r K τ := by
  rw [← fieldAut_mul_conjAut_mul_inv, inv_mul_cancel_right]

theorem conjAut_mul_fieldAut_pow (σ : K ≃+* K) (A : gsp r K) (k : ℕ) :
    (conjAut r K A * fieldAut r K σ) ^ k =
      conjAut r K (gspTwistedNorm σ A k) * fieldAut r K (σ ^ k) := by
  induction k with
  | zero => rw [pow_zero, gspTwistedNorm_zero, pow_zero, map_one, map_one, mul_one]
  | succ k ih =>
    rw [pow_succ, ih, gspTwistedNorm_succ, map_mul, pow_succ, map_mul (fieldAut r K)]
    calc conjAut r K (gspTwistedNorm σ A k) * fieldAut r K (σ ^ k) *
          (conjAut r K A * fieldAut r K σ) =
          conjAut r K (gspTwistedNorm σ A k) * (fieldAut r K (σ ^ k) * conjAut r K A) *
            fieldAut r K σ := by simp only [mul_assoc]
      _ = _ := by rw [fieldAut_mul_conjAut]; simp only [mul_assoc]

@[expose] def scalarGsp (b : Kˣ) : gsp r K :=
  ⟨GeneralLinearGroup.scalar (Fin r ⊕ Fin r) b, ⟨b * b, by
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_transpose,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, Units.val_mul]⟩⟩

theorem coe_scalarGsp (b : Kˣ) :
    ((scalarGsp b : gsp r K) : GL (Fin r ⊕ Fin r) K) =
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) b :=
  rfl

theorem scalar_mul_comm_gl (c : Kˣ) (g : GL (Fin r ⊕ Fin r) K) :
    GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c * g =
      g * GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  ext i j
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, mul_comm]

theorem scalarGsp_mul_comm (c : Kˣ) (g : gsp r K) : scalarGsp c * g = g * scalarGsp c :=
  Subtype.ext (scalar_mul_comm_gl (r := r) c (g : GL (Fin r ⊕ Fin r) K))

theorem gspFieldMap_scalarGsp (σ : K ≃+* K) (b : Kˣ) :
    gspFieldMap σ (scalarGsp b : gsp r K) = scalarGsp (Units.map (σ : K →* K) b) :=
  Subtype.ext (glFieldEquiv_scalar (Fin r ⊕ Fin r) σ b)

theorem gspTwistedNorm_scalarGsp_mul (σ : K ≃+* K) (b : Kˣ) (A : gsp r K) (k : ℕ) :
    gspTwistedNorm σ (scalarGsp b * A) k =
      scalarGsp (∏ i ∈ Finset.range k, Units.map ((σ ^ i : K ≃+* K) : K →* K) b) *
        gspTwistedNorm σ A k := by
  induction k with
  | zero =>
    rw [gspTwistedNorm_zero, gspTwistedNorm_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    exact Subtype.ext (by rw [coe_scalarGsp, map_one]; rfl)
  | succ k ih =>
    rw [gspTwistedNorm_succ, ih, gspFieldMap_mul, gspFieldMap_scalarGsp, gspTwistedNorm_succ,
      Finset.prod_range_succ]
    have e : (scalarGsp ((∏ i ∈ Finset.range k, Units.map ((σ ^ i : K ≃+* K) : K →* K) b) *
        Units.map ((σ ^ k : K ≃+* K) : K →* K) b) : gsp r K) =
        scalarGsp (∏ i ∈ Finset.range k, Units.map ((σ ^ i : K ≃+* K) : K →* K) b) *
          scalarGsp (Units.map ((σ ^ k : K ≃+* K) : K →* K) b) :=
      Subtype.ext (by rw [Subgroup.coe_mul, coe_scalarGsp, coe_scalarGsp, coe_scalarGsp, map_mul])
    rw [e, mul_assoc, ← mul_assoc (gspTwistedNorm σ A k),
      ← scalarGsp_mul_comm _ (gspTwistedNorm σ A k)]
    simp only [mul_assoc]

theorem conjAut_scalarGsp [Finite K] (hr : 1 ≤ r) (b : Kˣ) : conjAut r K (scalarGsp b) = 1 := by
  have h := (conjAut_mul_fieldAut_eq_one_iff hr (scalarGsp b) 1).mpr ⟨rfl, b, rfl⟩
  rwa [map_one, mul_one] at h

end Powers

section Semilinear

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spSemilin (σ : K ≃+* K) (B : GL (Fin r ⊕ Fin r) K) :
    (Fin r ⊕ Fin r → K) ≃+ (Fin r ⊕ Fin r → K) where
  toFun v := (B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ fun i => σ (v i)
  invFun w := fun i =>
    σ.symm ((((B⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w) i)
  left_inv v := by
    funext i
    have e : (((B⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        ((B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ fun i => σ (v i))) =
        fun i => σ (v i) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    simp only [e, RingEquiv.symm_apply_apply]
  right_inv w := by
    have e : (fun j => σ (σ.symm ((((B⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w) j))) =
        ((B⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w :=
      funext fun j => RingEquiv.apply_symm_apply _ _
    change (B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (fun j => σ (σ.symm
      ((((B⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w) j))) = w
    rw [e, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  map_add' v w := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp

theorem spSemilin_apply (σ : K ≃+* K) (B : GL (Fin r ⊕ Fin r) K) (v : Fin r ⊕ Fin r → K) :
    spSemilin σ B v = (B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ fun i => σ (v i) := rfl

theorem spSemilin_smul (σ : K ≃+* K) (B : GL (Fin r ⊕ Fin r) K) (c : K)
    (v : Fin r ⊕ Fin r → K) : spSemilin σ B (c • v) = σ c • spSemilin σ B v := by
  rw [spSemilin_apply, spSemilin_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem map_mulVec_ringEquiv' (σ : K ≃+* K) (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (w : Fin r ⊕ Fin r → K) : (fun i => σ ((M *ᵥ w) i)) = M.map σ *ᵥ fun i => σ (w i) :=
  funext fun i => RingHom.map_mulVec (σ : K →+* K) M w i

theorem iterate_spSemilin (σ : K ≃+* K) (A : gsp r K) (k : ℕ) (v : Fin r ⊕ Fin r → K) :
    (⇑(spSemilin σ (A : GL (Fin r ⊕ Fin r) K)))^[k] v =
      (((gspTwistedNorm σ A k : gsp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ fun i => (σ ^ k) (v i) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, gspTwistedNorm_zero, OneMemClass.coe_one, Units.val_one,
      Matrix.one_mulVec]
    rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, spSemilin_apply, map_mulVec_ringEquiv',
      Matrix.mulVec_mulVec, gspTwistedNorm_succ', Subgroup.coe_mul, Units.val_mul,
      coe_gspFieldMap]
    congr 1
    funext i
    rw [pow_succ']
    rfl

@[expose] def spForm (v w : Fin r ⊕ Fin r → K) : K := v ⬝ᵥ formJ r K *ᵥ w

theorem formJ_mulVec (v : Fin r ⊕ Fin r → K) :
    formJ r K *ᵥ v = Sum.elim (v ∘ Sum.inr) (-(v ∘ Sum.inl)) := by
  rw [formJ, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero]

theorem spForm_self (v : Fin r ⊕ Fin r → K) : spForm v v = 0 := by
  rw [spForm, formJ_mulVec]
  have hv : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := (Sum.elim_comp_inl_inr v).symm
  nth_rewrite 1 [hv]
  rw [sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_comm, add_neg_cancel]

theorem spForm_mulVec {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ : K}
    (hA : Aᵀ * formJ r K * A = μ • formJ r K) (v w : Fin r ⊕ Fin r → K) :
    spForm (A *ᵥ v) (A *ᵥ w) = μ * spForm v w := by
  rw [spForm, spForm, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hA, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem spForm_map (σ : K ≃+* K) (v w : Fin r ⊕ Fin r → K) :
    spForm (fun i => σ (v i)) (fun i => σ (w i)) = σ (spForm v w) := by
  have h : (fun i => σ ((formJ r K *ᵥ w) i)) = formJ r K *ᵥ fun i => σ (w i) := by
    rw [map_mulVec_ringEquiv', formJ_map]
  rw [spForm, spForm, ← h]
  simp only [dotProduct, map_sum, map_mul]

end Semilinear

section Gram

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

theorem dotProduct_gram_mulVec (B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (v w : Fin r ⊕ Fin r → K) :
    v ⬝ᵥ (Bᵀ * formJ r K * B) *ᵥ w = spForm (B *ᵥ v) (B *ᵥ w) := by
  rw [spForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem formJ_eq_neg_J : formJ r K = -Matrix.J (Fin r) K := by
  rw [formJ, Matrix.J, Matrix.fromBlocks_neg, neg_zero, neg_neg]

theorem det_formJ_ne_zero : (formJ r K).det ≠ 0 := by
  intro h
  have h1 := Matrix.J_det_mul_J_det (Fin r) K
  have h2 : (formJ r K).det = (Matrix.J (Fin r) K).det * (-1) ^ (r + r) := by
    rw [formJ_eq_neg_J, ← neg_one_smul K (Matrix.J (Fin r) K), Matrix.det_smul, Fintype.card_sum,
      Fintype.card_fin, mul_comm]
  rw [h2, (Even.add_self r).neg_one_pow, mul_one] at h
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

end Gram

section Main

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (conjAut_mul_fieldAut_eq_one_iff odd_symplectic_automorphism_semilinear_representation)

theorem symplectic_prime_semilinear_field_descent {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hr : 2 ≤ r) {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f) :
    (∀ A : gsp r K, conjAut r K A = 1 ↔
      ∃ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c) ∧
    Function.Injective (fieldAut r K) ∧
    spLinearAutGroup r K ⊓ (fieldAut r K).range = ⊥ ∧
    spLinearAutGroup r K ⊔ (fieldAut r K).range = spSemilinearAutGroup r K ∧
    ((spLinearAutGroup r K).subgroupOf (spSemilinearAutGroup r K)).Normal ∧
    (spLinearAutGroup r K).Normal ∧
    (∀ α β : MulAut (StatedProj (StatedSp r K)), α * β * α⁻¹ * β⁻¹ ∈ spLinearAutGroup r K) ∧
    (spSemilinearAutGroup r K).index ∣ 2 ∧
    (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣
      Nat.gcd 2 (ℓ ^ f - 1) ∧
    ∀ p : ℕ, p.Prime → ∀ a ∈ spSemilinearAutGroup r K, a ∉ spLinearAutGroup r K →
      orderOf a = p → p ∣ f ∧ ∃ σ : K ≃+* K, orderOf σ = p ∧
        Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p) ∧
        ∃ h ∈ spLinearAutGroup r K, a = h * fieldAut r K σ * h⁻¹ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : NeZero r := ⟨by omega⟩
  have hr1 : 1 ≤ r := by omega
  have hfaith := conjAut_mul_fieldAut_eq_one_iff (K := K) hr1
  have hker : ∀ A : gsp r K, conjAut r K A = 1 ↔
      ∃ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    intro A
    have h := hfaith A 1
    rw [map_one, mul_one] at h
    rw [h]
    exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  have hinj : Function.Injective (fieldAut r K) := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    exact ((hfaith 1 σ).mp (by rw [map_one, one_mul, hσ])).1
  have hDF : spLinearAutGroup r K ⊓ (fieldAut r K).range = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxD, σ, rfl⟩
    obtain ⟨A, hA⟩ := mem_spLinearAutGroup_iff.mp hxD
    have h1 : conjAut r K A⁻¹ * fieldAut r K σ = 1 := by rw [map_inv, hA, inv_mul_cancel]
    rw [((hfaith _ σ).mp h1).1, map_one]
    exact one_mem _
  have hDFE : spLinearAutGroup r K ⊔ (fieldAut r K).range = spSemilinearAutGroup r K := by
    rw [spSemilinearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_union, Subgroup.closure_eq,
      Subgroup.closure_eq]
  obtain ⟨-, -, hDnormE, -, hcycE, -⟩ := standard_outer_quotient (K := K) hr1
  have hHD := relIndex_inner_spLinearAutGroup_dvd (r := r) hℓ hf hK
  have hstruct : (spLinearAutGroup r K).Normal ∧
      (∀ α β : MulAut (StatedProj (StatedSp r K)), α * β * α⁻¹ * β⁻¹ ∈ spLinearAutGroup r K) ∧
      (spSemilinearAutGroup r K).index ∣ 2 := by
    by_cases hcase : ℓ = 2 ∧ r = 2
    · obtain ⟨rfl, rfl⟩ := hcase
      open CFSG.ComponentClassification.UnbalancedCatalog SpChain in
      obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ := even_symplectic_two_exterior_square_automorphism hf hK
      obtain ⟨-, -, -, huniq, -, -, -, -, hEsup, -, -, -⟩ := hall γ hγ
      have hDI : spLinearAutGroup 2 K = inner (StatedProj (StatedSp 2 K)) :=
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_symplectic_semilinear_normal_form
          (r := 2) hf hK).2.1
      have : (inner (StatedProj (StatedSp 2 K))).Normal := inner_normal _
      refine ⟨hDI ▸ inner_normal _, fun α β => hDI ▸ ?_, ?_⟩
      · refine commutator_mem_of_forall_zpow_mul_mem _ γ (fun x => ?_) α β
        obtain ⟨⟨g, j⟩, hx, -⟩ := huniq x
        refine ⟨-(j : ℤ), ?_⟩
        rw [hx]
        have h1 := (inner_normal (StatedProj (StatedSp 2 K))).conj_mem _
          (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.spInner_mem_inner g)
          (γ ^ (-(j : ℤ)))
        convert h1 using 1
        rw [_root_.zpow_neg, inv_inv, zpow_natCast, mul_assoc]
      · rw [Subgroup.index_dvd_two_iff]
        refine ⟨γ⁻¹, fun x => ?_⟩
        obtain ⟨⟨g, j⟩, hx, -⟩ := huniq x
        have hgE : CFSG.ComponentClassification.UnbalancedCatalog.SpChain.spInner 2 K g ∈
            spSemilinearAutGroup 2 K := by
          rw [hEsup]
          exact Subgroup.mem_sup_left
            (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.spInner_mem_inner g)
        have hγE : ∀ m : ℕ, γ ^ (2 * m) ∈ spSemilinearAutGroup 2 K := fun m => by
          rw [hEsup, pow_mul]
          exact Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers _ _)
        rw [hx]
        obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' (j : ℕ)
        · right
          rw [hm]
          exact mul_mem hgE (hγE m)
        · left
          rw [hm, pow_succ, mul_assoc, mul_inv_cancel_right]
          exact mul_mem hgE (hγE m)
    ·
      have hE : spSemilinearAutGroup r K = ⊤ := by
        by_cases hr3 : 3 ≤ r
        · exact (automorphism_generation (K := K) hr3).1
        · have hℓ2 : ℓ ≠ 2 := fun h => hcase ⟨h, by omega⟩
          have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
          rw [eq_top_iff]
          intro α _
          obtain ⟨A, σ, rfl⟩ := (odd_symplectic_automorphism_semilinear_representation hodd hr).1 α
          exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
            (fieldAut_mem_spSemilinearAutGroup σ)
      have hDn : (spLinearAutGroup r K).Normal := ⟨fun d hd g =>
        hDnormE.conj_mem ⟨d, spLinearAutGroup_le_spSemilinearAutGroup hd⟩ hd
          ⟨g, hE ▸ Subgroup.mem_top g⟩⟩
      obtain ⟨g, -, hg⟩ := hcycE
      refine ⟨hDn, commutator_mem_of_forall_zpow_mul_mem _ g
        fun x => hg x (hE ▸ Subgroup.mem_top x), by rw [hE, Subgroup.index_top]; exact one_dvd _⟩
  refine ⟨hker, hinj, hDF, hDFE, hDnormE, hstruct.1, hstruct.2.1, hstruct.2.2, hHD, ?_⟩
  intro p hp a haE haD hap
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨M, σ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp haE
  have hpow : conjAut r K (gspTwistedNorm σ M p) * fieldAut r K (σ ^ p) = 1 := by
    rw [← conjAut_mul_fieldAut_pow, ← hap, pow_orderOf_eq_one]
  obtain ⟨hσp, c, hc⟩ := (hfaith _ _).mp hpow
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply haD
    rw [map_one, mul_one]
    exact conjAut_mem_spLinearAutGroup M
  have hσ : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hNp : gspTwistedNorm σ M p = scalarGsp c := Subtype.ext hc
  have hσc : σ (c : K) = c := by
    have e1 := gspTwistedNorm_succ σ M p
    have e2 := gspTwistedNorm_succ' σ M p
    rw [hσp, gspFieldMap_one, hNp] at e1
    rw [hNp, gspFieldMap_scalarGsp] at e2
    have e3 : scalarGsp c * M = scalarGsp (Units.map (σ : K →* K) c) * M := by
      rw [← e1, e2, scalarGsp_mul_comm]
    have e4 := mul_right_cancel e3
    have e5 := congrArg (fun g : gsp r K => ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) e4
    simp only [coe_scalarGsp, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.coe_map] at e5
    exact e5.symm
  obtain ⟨b, hb⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ (c := (c : K)⁻¹)
    (by rw [map_inv₀, hσc])
  rw [hσ] at hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : ∏ i ∈ Finset.range p, (σ ^ i) (0 : K) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hp.pos) (by simp)
    rw [h0] at hb
    exact inv_ne_zero c.ne_zero hb.symm
  set A' : gsp r K := scalarGsp (Units.mk0 b hb0) * M with hA'
  have hcA' : conjAut r K A' = conjAut r K M := by
    rw [hA', map_mul, conjAut_scalarGsp hr1, one_mul]
  have hL' : gspTwistedNorm σ A' p = 1 := by
    rw [hA', gspTwistedNorm_scalarGsp_mul, hNp]
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_scalarGsp, coe_scalarGsp, ← map_mul, OneMemClass.coe_one,
      ← map_one (GeneralLinearGroup.scalar (Fin r ⊕ Fin r) : Kˣ →* GL (Fin r ⊕ Fin r) K)]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.coe_prod]
    simp only [Units.coe_map, Units.val_mk0, Units.val_one]
    change (∏ i ∈ Finset.range p, (σ ^ i) b) * c = 1
    rw [hb, inv_mul_cancel₀ c.ne_zero]
  set γ := spSemilin σ (A' : GL (Fin r ⊕ Fin r) K) with hγ
  have hγp : ∀ v, (⇑γ)^[p] v = v := fun v => by
    rw [hγ, iterate_spSemilin, hL', OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec, hσp]
    rfl
  obtain ⟨hpf, k₀, hk₀, hk₀card, bb, hbb, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis hℓ hf hK σ hσ
      (Module.finrank_fintype_fun_eq_card K) γ (spSemilin_smul σ _) hγp
  have hk₀mem : ∀ x : K, x ∈ k₀ ↔ σ x = x := fun x => Set.ext_iff.mp hk₀ x
  have hcard₀ : Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p) := by
    rw [← hk₀card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [hk₀mem]
      exact RingHom.mem_eqLocusField)
  refine ⟨hpf, σ, hσ, hcard₀, ?_⟩
  set bb' := bb.reindex (Fintype.equivFin (Fin r ⊕ Fin r)).symm with hbb'
  have hbb'fix : ∀ i, γ (bb' i) = bb' i := fun i => by
    rw [hbb', Module.Basis.reindex_apply, hbb]
  set Bm : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := Matrix.of fun i j => bb' j i with hBm
  set G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := Bmᵀ * formJ r K * Bm with hG
  have hcol : ∀ j, Bm *ᵥ Pi.single j 1 = bb' j := fun j => by
    ext k
    simp [hBm, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hGij : ∀ i j, G i j = spForm (bb' i) (bb' j) := fun i j => by
    rw [← hcol, ← hcol, ← dotProduct_gram_mulVec]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rfl
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A'.2
  have hγform : ∀ v w, spForm (γ v) (γ w) = (μ : K) * σ (spForm v w) := fun v w => by
    rw [hγ, spSemilin_apply, spSemilin_apply, spForm_mulVec hμ, spForm_map]
  have hGσ : ∀ i j, G i j = (μ : K) * σ (G i j) := fun i j => by
    rw [hGij, ← hγform, hbb'fix, hbb'fix]
  have hσG : ∀ i j, σ (G i j) = (μ : K)⁻¹ * G i j := fun i j => by
    rw [hGσ i j, ← mul_assoc, inv_mul_cancel₀ μ.ne_zero, one_mul, ← hGσ i j]
  have hBmT : Bm = (Pi.basisFun K (Fin r ⊕ Fin r)).toMatrix bb' := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rfl
  have hBm_det : Bm.det ≠ 0 := by
    intro h0
    have h1 : Bm * bb'.toMatrix (Pi.basisFun K (Fin r ⊕ Fin r)) = 1 := by
      rw [hBmT, Module.Basis.toMatrix_mul_toMatrix_flip]
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hGdet : G.det ≠ 0 := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hBm_det det_formJ_ne_zero) hBm_det
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨i₀, j₀, hx⟩ : ∃ i j, G i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hGdet
    have hG0 : G = 0 := Matrix.ext h
    rw [hG0, Matrix.det_zero]
  set x := G i₀ j₀ with hxdef
  have hσx : σ x = (μ : K)⁻¹ * x := hσG i₀ j₀
  have hG₀mem : ∀ i j, x⁻¹ * G i j ∈ k₀ := fun i j => by
    rw [hk₀mem, map_mul, map_inv₀, hσx, hσG]
    field_simp
  set G₀ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k₀ :=
    Matrix.of fun i j => ⟨x⁻¹ * G i j, hG₀mem i j⟩ with hG₀
  have hG₀map : G₀.map k₀.subtype = x⁻¹ • G := by
    ext i j
    rfl
  have halt₀ : ∀ v, v ⬝ᵥ G₀ *ᵥ v = 0 := fun v => by
    apply k₀.subtype.injective
    have h1 : (fun i => k₀.subtype ((G₀ *ᵥ v) i)) =
        G₀.map k₀.subtype *ᵥ fun i => k₀.subtype (v i) :=
      funext fun i => RingHom.map_mulVec k₀.subtype G₀ v i
    rw [map_zero, RingHom.map_dotProduct]
    change (fun i => k₀.subtype (v i)) ⬝ᵥ (fun i => k₀.subtype ((G₀ *ᵥ v) i)) = 0
    rw [h1, hG₀map, Matrix.smul_mulVec, dotProduct_smul, hG, dotProduct_gram_mulVec, spForm_self,
      smul_zero]
  have hdet₀ : G₀.det ≠ 0 := by
    intro h0
    have e1 : ((G₀.det : k₀) : K) = (G₀.map k₀.subtype).det := RingHom.map_det k₀.subtype G₀
    rw [h0, ZeroMemClass.coe_zero, hG₀map, Matrix.det_smul] at e1
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hx)) hGdet e1.symm
  obtain ⟨P, hPdet, hP⟩ := exists_transpose_mul_mul_eq_J G₀ halt₀ hdet₀
  set PK : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := P.map k₀.subtype with hPK
  set M₁ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := Bm * PK with hM₁
  have hPJ : PKᵀ * G₀.map k₀.subtype * PK = Matrix.J (Fin r) K := by
    have e := congrArg (fun X => X.map k₀.subtype) hP
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_J] at e
    exact e
  have hM₁J : M₁ᵀ * formJ r K * M₁ = (-x) • formJ r K := by
    calc M₁ᵀ * formJ r K * M₁ = PKᵀ * G * PK := by
          rw [hM₁, hG, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = PKᵀ * (x • G₀.map k₀.subtype) * PK := by
          rw [hG₀map, smul_smul, mul_inv_cancel₀ hx, one_smul]
      _ = x • (PKᵀ * G₀.map k₀.subtype * PK) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (-x) • formJ r K := by rw [hPJ, formJ_eq_neg_J, smul_neg, neg_smul, neg_neg]
  have hM₁det : M₁.det ≠ 0 := by
    rw [hM₁, Matrix.det_mul]
    refine mul_ne_zero hBm_det fun h => hPdet ?_
    have e1 : ((P.det : k₀) : K) = PK.det := RingHom.map_det k₀.subtype P
    rw [h] at e1
    exact (ZeroMemClass.coe_eq_zero).mp e1
  set M₁g : GL (Fin r ⊕ Fin r) K := GeneralLinearGroup.mkOfDetNeZero M₁ hM₁det with hM₁g
  have hM₁gsp : M₁g ∈ gsp r K := ⟨Units.mk0 (-x) (neg_ne_zero.mpr hx), by
    change M₁ᵀ * formJ r K * M₁ = ((Units.mk0 (-x) (neg_ne_zero.mpr hx) : Kˣ) : K) • formJ r K
    rw [Units.val_mk0]
    exact hM₁J⟩
  set N₁ : gsp r K := ⟨M₁g, hM₁gsp⟩ with hN₁
  have hcolM : ∀ j, (fun i => M₁ i j) = ∑ k, ((P k j : k₀) : K) • bb' k := fun j => by
    funext i
    simp only [hM₁, hBm, hPK, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hγcol : ∀ j, γ (fun i => M₁ i j) = fun i => M₁ i j := fun j => by
    rw [hcolM, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hPkj : σ ((P k j : k₀) : K) = (P k j : k₀) := (hk₀mem _).mp (P k j).2
    rw [hγ, spSemilin_smul, ← hγ, hbb'fix, hPkj]
  have hfixM : A' * gspFieldMap σ N₁ = N₁ := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    have := congrFun (hγcol j) i
    rw [hγ, spSemilin_apply] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hN₁, hM₁g, coe_gspFieldMap,
      CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv_entry] using this
  refine ⟨conjAut r K N₁, conjAut_mem_spLinearAutGroup N₁, ?_⟩
  have hA'eq : A' = N₁ * (gspFieldMap σ N₁)⁻¹ := eq_mul_inv_iff_mul_eq.mpr hfixM
  rw [← hcA', hA'eq, map_mul, map_inv, ← fieldAut_mul_conjAut_mul_inv σ N₁]
  group

end Main

end CFSG.RankThree.Classical.SteinbergBY
