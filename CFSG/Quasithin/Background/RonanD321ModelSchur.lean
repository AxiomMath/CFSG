module

public import CFSG.Open.StatedAPI
public import CFSG.Quasithin.Background.OperatorJordanHolder
public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90

public section

namespace CFSG.Quasithin.RonanD321.SL2Model

open Matrix CFSG.Open CFSG.Open.StatedAPI

variable {K : Type} [Field K]

abbrev slm (γ : ↥(StatedSL 2 K)) : Matrix (Fin 2) (Fin 2) K :=
  ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

@[expose] noncomputable def slMap (σ : K ≃+* K) : ↥(StatedSL 2 K) →* ↥(StatedSL 2 K) :=
  ((GeneralLinearGroup.map σ.toRingHom).comp (StatedSL 2 K).subtype).codRestrict
    (StatedSL 2 K) fun γ => by
      rw [mem_statedSL_iff]
      have e : ((((GeneralLinearGroup.map σ.toRingHom).comp (StatedSL 2 K).subtype) γ :
          GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = σ.toRingHom.mapMatrix (slm γ) := by
        ext i j
        simp [GeneralLinearGroup.map_apply]
      rw [e, ← RingHom.map_det, det_of_mem_statedSL γ.2, map_one]

theorem slm_slMap (σ : K ≃+* K) (γ : ↥(StatedSL 2 K)) : slm (slMap σ γ) = (slm γ).map σ := by
  ext i j
  rfl

theorem slMap_one (γ : ↥(StatedSL 2 K)) : slMap (1 : K ≃+* K) γ = γ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

theorem slMap_mul (σ τ : K ≃+* K) (γ : ↥(StatedSL 2 K)) :
    slMap (σ * τ) γ = slMap σ (slMap τ γ) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

theorem slm_injective : Function.Injective (slm (K := K)) := fun _ _ h =>
  Subtype.ext (Units.ext h)

@[expose] noncomputable def slOf (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) :
    ↥(StatedSL 2 K) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero A (by rw [hA]; exact one_ne_zero),
    mem_statedSL_iff.2 hA⟩

theorem slm_slOf (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) : slm (slOf A hA) = A := rfl

section Twisted

variable {α : ↥(StatedSL 2 K) → ↥(StatedSL 2 K)}

theorem injective_of_twisted {φ : (Fin 2 → K) →+ (Fin 2 → K)}
    (hφ : ∀ γ v, φ (slm γ *ᵥ v) = slm (α γ) *ᵥ φ v) {v₀ : Fin 2 → K} (hv₀ : φ v₀ ≠ 0) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  have hS : φ.ker = ⊤ := by
    refine eq_top_of_slMulVec_mem le_rfl (S := φ.ker) (fun γ w hw => ?_)
      (AddMonoidHom.mem_ker.2 hv) hne
    rw [AddMonoidHom.mem_ker] at hw ⊢
    rw [hφ, hw, mulVec_zero]
  exact hv₀ (AddMonoidHom.mem_ker.1 (hS ▸ AddSubgroup.mem_top v₀))

variable [Finite K]

theorem exists_smul_of_twisted (hα : Function.Surjective α) {φ ψ : (Fin 2 → K) →+ (Fin 2 → K)}
    (hφ : ∀ γ v, φ (slm γ *ᵥ v) = slm (α γ) *ᵥ φ v) (hφi : Function.Injective φ)
    (hψ : ∀ γ v, ψ (slm γ *ᵥ v) = slm (α γ) *ᵥ ψ v) :
    ∃ μ : K, ∀ v, ψ v = μ • φ v := by
  let e : (Fin 2 → K) ≃+ (Fin 2 → K) :=
    AddEquiv.ofBijective φ ⟨hφi, Finite.surjective_of_injective hφi⟩
  have he : ∀ v, e v = φ v := fun v => rfl
  have hinv : ∀ γ u, e.symm (slm (α γ) *ᵥ u) = slm γ *ᵥ e.symm u := by
    intro γ u
    rw [AddEquiv.symm_apply_eq, he, hφ, ← he, AddEquiv.apply_symm_apply]
  obtain ⟨μ, hμ⟩ := exists_smul_of_comm_sl le_rfl (ψ.comp e.symm.toAddMonoidHom) (by
    intro δ u
    obtain ⟨γ, rfl⟩ := hα δ
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [hinv, hψ])
  refine ⟨μ, fun v => ?_⟩
  have h := hμ (φ v)
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] at h
  rwa [← he, AddEquiv.symm_apply_apply] at h

theorem exists_ringEquiv_of_twisted (hα : Function.Surjective α)
    {φ : (Fin 2 → K) →+ (Fin 2 → K)} (hφ : ∀ γ v, φ (slm γ *ᵥ v) = slm (α γ) *ᵥ φ v)
    (hφi : Function.Injective φ) :
    ∃ σ : K ≃+* K, ∀ (c : K) v, φ (c • v) = σ c • φ v := by
  have hc : ∀ c : K, ∃ μ : K, ∀ v, φ (c • v) = μ • φ v := by
    intro c
    refine exists_smul_of_twisted hα (ψ := φ.comp (DistribSMul.toAddMonoidHom (Fin 2 → K) c))
      hφ hφi ?_
    intro γ v
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [← mulVec_smul, hφ]
  choose s hs using hc
  have hy0 : φ (Pi.single 0 1) ≠ 0 := by
    intro h0
    have h1 : Pi.single (0 : Fin 2) (1 : K) = 0 := hφi (h0.trans (map_zero φ).symm)
    have h2 := congrFun h1 0
    simp at h2
  have key : ∀ a b : K, a • φ (Pi.single 0 1) = b • φ (Pi.single 0 1) → a = b :=
    fun a b h => smul_left_injective K hy0 h
  let f : K →+* K :=
    { toFun := s
      map_one' := key _ _ (by rw [← hs]; simp)
      map_mul' := fun a b => key _ _ (by rw [← hs, mul_smul a b, hs, hs, mul_smul])
      map_zero' := key _ _ (by rw [← hs]; simp)
      map_add' := fun a b => key _ _ (by rw [← hs, add_smul a b, map_add, hs, hs, add_smul]) }
  exact ⟨RingEquiv.ofBijective f ⟨f.injective, Finite.surjective_of_injective f.injective⟩,
    fun c v => hs c v⟩

end Twisted

theorem eq_mulVec_of_semilinear (σ : K ≃+* K) {φ : (Fin 2 → K) →+ (Fin 2 → K)}
    (hφ : ∀ (c : K) v, φ (c • v) = σ c • φ v) (v : Fin 2 → K) :
    φ v = (Matrix.of fun i j => φ (Pi.single j 1) i) *ᵥ (σ ∘ v) := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv, map_add, hφ, hφ]
  ext i
  simp [mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

@[expose] def blk (Φ : Matrix (Fin 2) (Fin 2) K →+ Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (Fin 2 → K) →+ (Fin 2 → K) :=
  AddMonoidHom.mk' (fun v k => Φ (vecMulVec v (Pi.single j 1)) k i) fun v w => by
    ext k
    simp [add_vecMulVec]

theorem blk_apply (Φ : Matrix (Fin 2) (Fin 2) K →+ Matrix (Fin 2) (Fin 2) K) (i j : Fin 2)
    (v : Fin 2 → K) (k : Fin 2) : blk Φ i j v k = Φ (vecMulVec v (Pi.single j 1)) k i := rfl

theorem blk_twisted {α : ↥(StatedSL 2 K) → ↥(StatedSL 2 K)}
    {Φ : Matrix (Fin 2) (Fin 2) K →+ Matrix (Fin 2) (Fin 2) K}
    (htw : ∀ γ X, Φ (slm γ * X) = slm (α γ) * Φ X) (i j : Fin 2) (γ : ↥(StatedSL 2 K))
    (v : Fin 2 → K) : blk Φ i j (slm γ *ᵥ v) = slm (α γ) *ᵥ blk Φ i j v := by
  ext k
  rw [blk_apply, ← mul_vecMulVec, htw]
  simp [mul_apply, mulVec, dotProduct, blk_apply]

theorem apply_eq_blk (Φ : Matrix (Fin 2) (Fin 2) K →+ Matrix (Fin 2) (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) (k i : Fin 2) :
    Φ X k i = blk Φ i 0 (fun l => X l 0) k + blk Φ i 1 (fun l => X l 1) k := by
  have hX : X = vecMulVec (fun l => X l 0) (Pi.single 0 1) +
      vecMulVec (fun l => X l 1) (Pi.single 1 1) := by
    ext a b
    fin_cases b <;> simp [vecMulVec]
  conv_lhs => rw [hX]
  rw [map_add]
  rfl

theorem exists_semilinear_form [Finite K] {α : ↥(StatedSL 2 K) → ↥(StatedSL 2 K)}
    (Φ : Matrix (Fin 2) (Fin 2) K →+ Matrix (Fin 2) (Fin 2) K) (hΦ : Function.Injective Φ)
    (hα : Function.Surjective α) (htw : ∀ γ X, Φ (slm γ * X) = slm (α γ) * Φ X) :
    ∃ (σ : K ≃+* K) (A B : Matrix (Fin 2) (Fin 2) K), IsUnit A ∧ IsUnit B ∧
      (∀ X, Φ X = A * X.map σ * B) ∧ ∀ γ, slm (α γ) * A = A * (slm γ).map σ := by
  have hE : Φ (vecMulVec (Pi.single 0 1) (Pi.single 0 1)) ≠ 0 := by
    intro h0
    have h1 := hΦ (h0.trans (map_zero Φ).symm)
    have h2 := congrFun (congrFun h1 0) 0
    simp [vecMulVec] at h2
  obtain ⟨k₀, i₀, hki⟩ : ∃ k i, Φ (vecMulVec (Pi.single 0 1) (Pi.single 0 1)) k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hE (Matrix.ext h)
  have hφtw := blk_twisted htw i₀ 0
  have hφ0 : blk Φ i₀ 0 (Pi.single 0 1) ≠ 0 := fun h => hki (by
    have := congrFun h k₀
    rwa [blk_apply] at this)
  have hφi := injective_of_twisted hφtw hφ0
  have hμ : ∀ i j, ∃ μ : K, ∀ v, blk Φ i j v = μ • blk Φ i₀ 0 v :=
    fun i j => exists_smul_of_twisted hα hφtw hφi (blk_twisted htw i j)
  choose μ hμ using hμ
  generalize blk Φ i₀ 0 = φ at hφtw hφ0 hφi hμ
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_twisted hα hφtw hφi
  have hφA : ∀ v, φ v = (Matrix.of fun a b => φ (Pi.single b 1) a) *ᵥ (σ ∘ v) :=
    eq_mulVec_of_semilinear σ hσ
  generalize Matrix.of (fun a b => φ (Pi.single b 1) a) = A at hφA
  have hform : ∀ X, Φ X = A * X.map σ * Matrix.of (fun j i => μ i j) := by
    intro X
    ext k i
    rw [apply_eq_blk, hμ i 0, hμ i 1, Pi.smul_apply, Pi.smul_apply, hφA, hφA]
    simp [mul_apply, mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hAu : IsUnit A := by
    rw [← mulVec_surjective_iff_isUnit]
    intro w
    obtain ⟨u, hu⟩ := Finite.surjective_of_injective hφi w
    exact ⟨σ ∘ u, by rw [← hφA, hu]⟩
  have hBu : IsUnit (Matrix.of fun j i => μ i j) := by
    obtain ⟨X, hX⟩ := Finite.surjective_of_injective hΦ (1 : Matrix (Fin 2) (Fin 2) K)
    rw [hform] at hX
    have hdet := congrArg Matrix.det hX
    rw [det_mul, det_one] at hdet
    rw [isUnit_iff_isUnit_det]
    exact IsUnit.of_mul_eq_one_right _ hdet
  refine ⟨σ, A, _, hAu, hBu, hform, fun γ => ?_⟩
  refine Matrix.ext_of_mulVec_single fun b => ?_
  have hsb : σ ∘ (Pi.single b (1 : K)) = Pi.single b 1 := by
    ext l
    by_cases h : l = b
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← hsb, ← hφA, ← hφtw, hφA]
  congr 1
  ext l
  exact RingHom.map_mulVec σ.toRingHom (slm γ) (Pi.single b 1) l

theorem exists_det_one [Finite K] (hK : ringChar K = 2) {A : Matrix (Fin 2) (Fin 2) K}
    (hA : IsUnit A) : ∃ μ : K, μ ≠ 0 ∧ (μ⁻¹ • A).det = 1 := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hK A.det
  have hd : A.det ≠ 0 := ((isUnit_iff_isUnit_det A).1 hA).ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact hd hr
  refine ⟨r, hr0, ?_⟩
  rw [det_smul, Fintype.card_fin, hr]
  field_simp

theorem eq_one_of_conj (τ : K ≃+* K) {δ : Matrix (Fin 2) (Fin 2) K} (hδ : IsUnit δ)
    (h : ∀ γ : ↥(StatedSL 2 K), δ * slm γ = (slm γ).map τ * δ) : τ = 1 := by
  obtain ⟨u, rfl⟩ := hδ
  ext c
  have hdet : (!![c, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [det_fin_two_of]
  have h1 := h (slOf _ hdet)
  rw [slm_slOf] at h1
  have h2 : (!![c, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).map τ =
      (u : Matrix (Fin 2) (Fin 2) K) * !![c, 1; -1, 0] * ((u⁻¹ : (Matrix (Fin 2) (Fin 2) K)ˣ) :
        Matrix (Fin 2) (Fin 2) K) := by
    rw [h1, mul_assoc, Units.mul_inv, mul_one]
  have h3 := congrArg Matrix.trace h2
  rw [trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul] at h3
  simpa [trace_fin_two] using h3

theorem exists_smul_one_of_forall {P : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ r : Fin 2 → K, ∃ c : K, P *ᵥ r = c • r) : ∃ c : K, P = c • 1 := by
  obtain ⟨a, ha⟩ := h (Pi.single 0 1)
  obtain ⟨b, hb⟩ := h (Pi.single 1 1)
  obtain ⟨c, hc⟩ := h (fun _ => 1)
  have ha1 := congrFun ha 1
  have hb0 := congrFun hb 0
  have hc0 := congrFun hc 0
  have hc1 := congrFun hc 1
  simp [mulVec, dotProduct, Fin.sum_univ_two] at ha1 hb0 hc0 hc1
  refine ⟨c, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination hc0 - hb0
  · exact hb0
  · exact ha1
  · linear_combination hc1 - ha1

theorem exists_fixed_vec [Finite K] (σ : K ≃+* K) {C : Matrix (Fin 2) (Fin 2) K} (hC : IsUnit C)
    {c : K} (hc : HardMathSupport.Foote.ModuleExclusions.Ai σ C (orderOf σ) = c • 1) :
    ∃ b : Fin 2 → K, b ≠ 0 ∧ ∃ l : K, C *ᵥ (σ ∘ b) = l • b := by
  have hCd : C.det ≠ 0 := ((isUnit_iff_isUnit_det C).1 hC).ne_zero
  obtain ⟨l, B, hl, hB, hCB⟩ :=
    HardMathSupport.Foote.ModuleExclusions.hilbert90_matrix σ C hCd c hc
  refine ⟨fun k => B k 0, ?_, l⁻¹, ?_⟩
  · intro h0
    apply hB
    have h00 : B 0 0 = 0 := congrFun h0 0
    have h10 : B 1 0 = 0 := congrFun h0 1
    rw [det_fin_two, h00, h10]
    ring
  · ext k
    have h := congrFun (congrFun hCB k) 0
    simp [mul_apply, mulVec, dotProduct, Fin.sum_univ_two] at h ⊢
    rw [← h]
    field_simp

theorem isCyclic_ringEquiv [Finite K] : IsCyclic (K ≃+* K) := by
  let _ : Fintype K := Fintype.ofFinite K
  haveI := ringChar.charP K
  obtain ⟨n, hp, -⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  let e : (K ≃+* K) ≃* (K ≃ₐ[ZMod (ringChar K)] K) :=
    { toFun := fun σ =>
        AlgEquiv.ofRingEquiv (f := σ) (by
          intro x
          have h : (σ.toRingHom.comp (algebraMap (ZMod (ringChar K)) K) :
              ZMod (ringChar K) →+* K) = algebraMap (ZMod (ringChar K)) K :=
            RingHom.ext_zmod _ _
          exact DFunLike.congr_fun h x)
      invFun := fun σ => σ.toRingEquiv
      left_inv := by intro σ; ext x; rfl
      right_inv := by intro σ; ext x; rfl
      map_mul' := by intro σ τ; ext x; rfl }
  exact e.isCyclic.mpr inferInstance

theorem map_vecMulVec (σ : K ≃+* K) (v r : Fin 2 → K) :
    (vecMulVec v r).map σ = vecMulVec (σ ∘ v) (σ ∘ r) := by
  ext i j
  simp [vecMulVec]

theorem mul_vecMulVec_mul (A B : Matrix (Fin 2) (Fin 2) K) (v r : Fin 2 → K) :
    A * vecMulVec v r * B = vecMulVec (A *ᵥ v) (Bᵀ *ᵥ r) := by
  rw [mul_vecMulVec, vecMulVec_mul, mulVec_transpose]

theorem eq_smul_of_vecMulVec_eq {v r s : Fin 2 → K}
    (h : vecMulVec v r = vecMulVec (Pi.single 0 1) s) : s = v 0 • r := by
  ext j
  have h1 := congrFun (congrFun h 0) j
  simp [vecMulVec] at h1
  rw [Pi.smul_apply, smul_eq_mul, h1]

end CFSG.Quasithin.RonanD321.SL2Model
