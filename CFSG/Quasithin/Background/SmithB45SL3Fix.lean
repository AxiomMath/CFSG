module

public import CFSG.Quasithin.Background.SmithB42SL3Base
public import CFSG.Quasithin.Background.SmithB42SL3Trace

public section

namespace CFSG.Quasithin

namespace B45SL3

open CFSG.QuasithinUnique.Setup.X7a CFSG.Semidihedral.Principal Matrix
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply MatIso)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep repFixedSpace mem_repFixedSpace)
open CFSG.Quasithin.B42SL3 (IsSingle exists_idx_two tensorRepGen_apply_two subsingleton_of_trivial
  locDim_pos)
open scoped MatrixGroups Matrix

section Pair

variable {k G : Type} [Field k] [Group G]

theorem finrank_repFixedSpace_equiv {V W : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) (A : Set G) :
    Module.finrank k (repFixedSpace ρ A) = Module.finrank k (repFixedSpace σ A) := by
  have hmap : (repFixedSpace ρ A).map e.toLinearEquiv.toLinearMap = repFixedSpace σ A := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine mem_repFixedSpace.mpr fun a ha => ?_
      have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap a v
      have h2 : ρ a v = v := mem_repFixedSpace.mp hv a ha
      rw [h2] at h1
      exact h1.symm
    · intro hw
      refine ⟨e.toLinearEquiv.symm w, mem_repFixedSpace.mpr fun a ha => ?_,
        e.toLinearEquiv.apply_symm_apply w⟩
      apply e.toLinearEquiv.injective
      have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap a
        (e.toLinearEquiv.symm w)
      have h3 : e.toIntertwiningMap (e.toLinearEquiv.symm w) = w :=
        e.toLinearEquiv.apply_symm_apply w
      change e.toIntertwiningMap (ρ a (e.toLinearEquiv.symm w)) =
        e.toLinearEquiv (e.toLinearEquiv.symm w)
      rw [h1, h3, mem_repFixedSpace.mp hw a ha]
      exact (e.toLinearEquiv.apply_symm_apply w).symm
  rw [← hmap, LinearEquiv.finrank_map_eq]

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem repFixedSpace_comp (R : G →* Matrix κ κ k) (α : G →* G) (A : Set G) :
    repFixedSpace (matRep (R.comp α)) A = repFixedSpace (matRep R) (α '' A) := by
  ext v
  simp only [mem_repFixedSpace, matRep_apply, MonoidHom.comp_apply, Set.mem_image,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

theorem rank_add_one_le_codim (R : G →* Matrix κ κ k) {s₀ s₁ : G} {v : κ → k}
    (hv₀ : R s₀ *ᵥ v = v) (hv₁ : R s₁ *ᵥ v ≠ v) :
    (R s₀ - 1).rank + 1 ≤
      Module.finrank k (κ → k) - Module.finrank k (repFixedSpace (matRep R) {s₀, s₁}) := by
  have hle : repFixedSpace (matRep R) {s₀, s₁} ≤ repFixedSpace (matRep R) {s₀} := by
    intro w hw
    exact mem_repFixedSpace.mpr fun a ha => mem_repFixedSpace.mp hw a
      (by rw [Set.mem_singleton_iff.mp ha]; exact Set.mem_insert _ _)
  have hlt : repFixedSpace (matRep R) {s₀, s₁} < repFixedSpace (matRep R) {s₀} := by
    refine lt_of_le_of_ne hle fun heq => hv₁ ?_
    have hvmem : v ∈ repFixedSpace (matRep R) {s₀} :=
      mem_repFixedSpace.mpr fun a ha => by rw [Set.mem_singleton_iff.mp ha]; exact hv₀
    rw [← heq] at hvmem
    exact mem_repFixedSpace.mp hvmem s₁ (Set.mem_insert_of_mem _ rfl)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := CFSG.QuasithinUnique.Setup.X7b.fixedCodim_matRep R s₀
  have h3 := Submodule.finrank_le (repFixedSpace (matRep R) {s₀})
  omega

end Pair

section Two

variable {F : Type} [Field F] [CharP F 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  (τ : ι → Bool × Bool) (e : ι → ℕ) {i i' : ι}

omit [Fintype ι] in
theorem bijective_pair (hii' : i ≠ i') (hrest : ∀ p, p ≠ i → p ≠ i' → τ p = (false, false)) :
    Function.Bijective (fun y : (∀ p, Fin (locDim (τ p).1 (τ p).2)) => (y i, y i')) := by
  constructor
  · intro y z h
    simp only [Prod.mk.injEq] at h
    funext p
    by_cases hpi : p = i
    · subst hpi
      exact h.1
    by_cases hpi' : p = i'
    · subst hpi'
      exact h.2
    exact (subsingleton_of_trivial (hrest p hpi hpi')).elim _ _
  · rintro ⟨c, c'⟩
    obtain ⟨y, hy, hy'⟩ := exists_idx_two τ hii' c c'
    exact ⟨y, Prod.ext hy hy'⟩

theorem mulVec_lift_two (hii' : i ≠ i') (hrest : ∀ p, p ≠ i → p ≠ i' → τ p = (false, false))
    (g : SL(3, F)) (w : Fin (locDim (τ i).1 (τ i).2) → Fin (locDim (τ i').1 (τ i').2) → F)
    (y : ∀ p, Fin (locDim (τ p).1 (τ p).2)) :
    (tensorRepGen F τ e g *ᵥ fun z => w (z i) (z i')) y =
      ∑ c, ∑ c', locRep F (τ i).1 (τ i).2 (e i) g (y i) c *
        locRep F (τ i').1 (τ i').2 (e i') g (y i') c' * w c c' := by
  classical
  set E := Equiv.ofBijective _ (bijective_pair τ hii' hrest) with hE
  rw [Matrix.mulVec, dotProduct]
  simp_rw [tensorRepGen_apply_two τ e hii' hrest]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv E _ _ fun z => rfl

end Two

section Local

variable {F : Type} [Field F] [CharP F 2]

theorem natRep_up3 (j : ℕ) (x y z : F) :
    natRep F j (up3 x y z) = upMat (frK F j x) (frK F j y) (frK F j z) :=
  twistMat_up3 F j x y z

theorem dualRep_up3 (j : ℕ) (x y z : F) :
    dualRep F j (up3 x y z) = (upMat (frK F j x) (frK F j (y + z * x)) (frK F j z))ᵀ := by
  rw [dualRep_apply, up3_inv, twistMat_up3]

@[expose] def stdC (F : Type) [Field F] : SL(3, F) × SL(3, F) := (up3 0 0 1, up3 0 1 0)

@[expose] def stdA (F : Type) [Field F] : SL(3, F) × SL(3, F) := (up3 0 1 0, up3 1 0 0)

@[expose] def GoodVec (L L' : SL(3, F) →* Matrix (Fin 3) (Fin 3) F) (s : SL(3, F) × SL(3, F)) :
    Prop :=
  ∃ w : Fin 3 → Fin 3 → F,
    (∀ c c' : Fin 3, ∑ d : Fin 3, ∑ d' : Fin 3, L s.1 c d * L' s.1 c' d' * w d d' = w c c') ∧
    (∃ c c' : Fin 3, ∑ d : Fin 3, ∑ d' : Fin 3, L s.2 c d * L' s.2 c' d' * w d d' ≠ w c c')

theorem goodVec_nat_nat_C (j j' : ℕ) : GoodVec (natRep F j) (natRep F j') (stdC F) := by
  refine ⟨!![0, 0, 0; 0, 0, 0; 0, 0, 1], fun c c' => ?_, 0, 0, ?_⟩
  · simp only [stdC]
    rw [natRep_up3, natRep_up3]
    fin_cases c <;> fin_cases c' <;> simp [Fin.sum_univ_three, upMat]
  · simp only [stdC]
    rw [natRep_up3, natRep_up3]
    simp [Fin.sum_univ_three, upMat]

theorem goodVec_nat_nat_A (j j' : ℕ) : GoodVec (natRep F j) (natRep F j') (stdA F) := by
  refine ⟨!![0, 0, 1; 0, 0, 0; 1, 0, 0], fun c c' => ?_, 1, 0, ?_⟩
  · simp only [stdA]
    rw [natRep_up3, natRep_up3]
    fin_cases c <;> fin_cases c' <;> simp [Fin.sum_univ_three, upMat, CharTwo.add_self_eq_zero]
  · simp only [stdA]
    rw [natRep_up3, natRep_up3]
    simp [Fin.sum_univ_three, upMat]

theorem goodVec_nat_dual_C (j j' : ℕ) : GoodVec (natRep F j) (dualRep F j') (stdC F) := by
  refine ⟨!![0, 0, 0; 0, 0, 0; 0, 0, 1], fun c c' => ?_, 0, 2, ?_⟩
  · simp only [stdC]
    rw [natRep_up3, dualRep_up3]
    fin_cases c <;> fin_cases c' <;> simp [Fin.sum_univ_three, upMat]
  · simp only [stdC]
    rw [natRep_up3, dualRep_up3]
    simp [Fin.sum_univ_three, upMat]

theorem goodVec_nat_dual_A (j j' : ℕ) : GoodVec (natRep F j) (dualRep F j') (stdA F) := by
  refine ⟨!![0, 1, 0; 0, 0, 0; 0, 0, 0], fun c c' => ?_, 0, 2, ?_⟩
  · simp only [stdA]
    rw [natRep_up3, dualRep_up3]
    fin_cases c <;> fin_cases c' <;> simp [Fin.sum_univ_three, upMat]
  · simp only [stdA]
    rw [natRep_up3, dualRep_up3]
    simp [Fin.sum_univ_three, upMat]

theorem goodVec_dual_nat_C (j j' : ℕ) : GoodVec (dualRep F j) (natRep F j') (stdC F) := by
  refine ⟨!![0, 0, 0; 0, 0, 0; 0, 0, 1], fun c c' => ?_, 2, 0, ?_⟩
  · simp only [stdC]
    rw [dualRep_up3, natRep_up3]
    fin_cases c <;> fin_cases c' <;> simp [Fin.sum_univ_three, upMat]
  · simp only [stdC]
    rw [dualRep_up3, natRep_up3]
    simp [Fin.sum_univ_three, upMat]

theorem goodVec_dual_nat_A (j j' : ℕ) : GoodVec (dualRep F j) (natRep F j') (stdA F) := by
  refine ⟨!![0, 0, 0; 1, 0, 0; 0, 0, 0], fun c c' => ?_, 2, 0, ?_⟩
  · simp only [stdA]
    rw [dualRep_up3, natRep_up3]
    fin_cases c <;> fin_cases c' <;> simp [Fin.sum_univ_three, upMat]
  · simp only [stdA]
    rw [dualRep_up3, natRep_up3]
    simp [Fin.sum_univ_three, upMat]

theorem goodVec_dual_dual_C (j j' : ℕ) : GoodVec (dualRep F j) (dualRep F j') (stdC F) := by
  refine ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 0], fun c c' => ?_, 2, 1, ?_⟩
  · simp only [stdC]
    rw [dualRep_up3, dualRep_up3]
    fin_cases c <;> fin_cases c' <;> simp [Fin.sum_univ_three, upMat, CharTwo.add_self_eq_zero]
  · simp only [stdC]
    rw [dualRep_up3, dualRep_up3]
    simp [Fin.sum_univ_three, upMat]

theorem goodVec_dual_dual_A (j j' : ℕ) : GoodVec (dualRep F j) (dualRep F j') (stdA F) := by
  refine ⟨!![0, 0, 0; 0, 1, 0; 0, 0, 0], fun c c' => ?_, 2, 2, ?_⟩
  · simp only [stdA]
    rw [dualRep_up3, dualRep_up3]
    fin_cases c <;> fin_cases c' <;> simp [Fin.sum_univ_three, upMat]
  · simp only [stdA]
    rw [dualRep_up3, dualRep_up3]
    simp [Fin.sum_univ_three, upMat]

theorem exists_vec_kron {ℓ ℓ' : Bool × Bool} (hℓ : IsSingle ℓ) (hℓ' : IsSingle ℓ') (j j' : ℕ)
    {s : SL(3, F) × SL(3, F)} (hs : s = stdC F ∨ s = stdA F) :
    ∃ w : Fin (locDim ℓ.1 ℓ.2) → Fin (locDim ℓ'.1 ℓ'.2) → F,
      (∀ c c', ∑ d, ∑ d', locRep F ℓ.1 ℓ.2 j s.1 c d * locRep F ℓ'.1 ℓ'.2 j' s.1 c' d' *
        w d d' = w c c') ∧
      (∃ c c', ∑ d, ∑ d', locRep F ℓ.1 ℓ.2 j s.2 c d * locRep F ℓ'.1 ℓ'.2 j' s.2 c' d' *
        w d d' ≠ w c c') := by
  rcases hℓ with rfl | rfl <;> rcases hℓ' with rfl | rfl <;> rcases hs with rfl | rfl
  · exact goodVec_nat_nat_C j j'
  · exact goodVec_nat_nat_A j j'
  · exact goodVec_nat_dual_C j j'
  · exact goodVec_nat_dual_A j j'
  · exact goodVec_dual_nat_C j j'
  · exact goodVec_dual_nat_A j j'
  · exact goodVec_dual_dual_C j j'
  · exact goodVec_dual_dual_A j j'


theorem adjRep_mulVec (j : ℕ) (g : SL(3, F)) (c : Fin 8 → F) :
    adjRep F j g *ᵥ c = co (conjMat F j g (Xm c)) := by
  have h := Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' (adjEnd F j g)
  have h2 : adjRep F j g *ᵥ c = Matrix.toLinAlgEquiv' (adjRep F j g) c := rfl
  rw [h2]
  change Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' (adjEnd F j g)) c = _
  rw [h, adjEnd_apply]

theorem exists_vec_adj (j : ℕ) {s : SL(3, F) × SL(3, F)} (hs : s = stdC F ∨ s = stdA F) :
    ∃ w : Fin 8 → F, adjRep F j s.1 *ᵥ w = w ∧ adjRep F j s.2 *ᵥ w ≠ w := by
  rcases hs with rfl | rfl
  · refine ⟨Pi.single 6 1, ?_, ?_⟩
    · simp only [stdC]
      rw [adjRep_mulVec, conjMat, up3_inv, twistMat_up3, twistMat_up3]
      funext r
      fin_cases r <;> simp [co, Xm, upMat, Matrix.mul_apply, Fin.sum_univ_three]
    · simp only [stdC]
      rw [adjRep_mulVec, conjMat, up3_inv, twistMat_up3, twistMat_up3]
      intro h
      have := congrFun h 3
      simp [co, Xm, upMat, Matrix.mul_apply, Fin.sum_univ_three] at this
  · refine ⟨Pi.single 3 1, ?_, ?_⟩
    · simp only [stdA]
      rw [adjRep_mulVec, conjMat, up3_inv, twistMat_up3, twistMat_up3]
      funext r
      fin_cases r <;> simp [co, Xm, upMat, Matrix.mul_apply, Fin.sum_univ_three]
    · simp only [stdA]
      rw [adjRep_mulVec, conjMat, up3_inv, twistMat_up3, twistMat_up3]
      intro h
      have := congrFun h 0
      simp [co, Xm, upMat, Matrix.mul_apply, Fin.sum_univ_three] at this

end Local


section Std

variable {F : Type} [Field F] [CharP F 2]

@[expose] def IsRootPair (t₁ t₂ : SL(3, F)) : Prop :=
  (∃ c φ₁ φ₂ : Fin 3 → F, c ≠ 0 ∧ φ₁ ⬝ᵥ c = 0 ∧ φ₂ ⬝ᵥ c = 0 ∧
      LinearIndependent F ![φ₁, φ₂] ∧
      (t₁ : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec c φ₁ ∧
      (t₂ : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec c φ₂) ∨
    (∃ ψ w₁ w₂ : Fin 3 → F, ψ ≠ 0 ∧ ψ ⬝ᵥ w₁ = 0 ∧ ψ ⬝ᵥ w₂ = 0 ∧
      LinearIndependent F ![w₁, w₂] ∧
      (t₁ : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec w₁ ψ ∧
      (t₂ : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec w₂ ψ)

omit [CharP F 2] in
theorem exists_dotProduct_eq_one {c : Fin 3 → F} (hc : c ≠ 0) : ∃ ψ : Fin 3 → F, ψ ⬝ᵥ c = 1 := by
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  refine ⟨Pi.single j (c j)⁻¹, ?_⟩
  rw [single_dotProduct, inv_mul_cancel₀ hj]

omit [CharP F 2] in
theorem linearIndependent_three {c ψ₀ φ₁ φ₂ : Fin 3 → F} (h0 : ψ₀ ⬝ᵥ c = 1)
    (h1 : φ₁ ⬝ᵥ c = 0) (h2 : φ₂ ⬝ᵥ c = 0) (hind : LinearIndependent F ![φ₁, φ₂]) :
    LinearIndependent F ![ψ₀, φ₁, φ₂] := by
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro g hg
  have hg' : g 0 • ψ₀ + g 1 • φ₁ + g 2 • φ₂ = 0 := by
    simpa [Fin.sum_univ_three] using hg
  have hg0 : g 0 = 0 := by
    have := congrArg (fun v => v ⬝ᵥ c) hg'
    simpa [add_dotProduct, smul_dotProduct, h0, h1, h2] using this
  have hrest := hind ![g 1, g 2] (by
    rw [hg0, zero_smul, zero_add] at hg'
    simpa [Fin.sum_univ_two] using hg')
  intro r
  fin_cases r
  · exact hg0
  · exact hrest 0
  · exact hrest 1

omit [CharP F 2] in
theorem exists_conj_std {t₁ t₂ : SL(3, F)} (h : IsRootPair t₁ t₂) :
    ∃ (A : GL (Fin 3) F) (s : SL(3, F) × SL(3, F)), (s = stdC F ∨ s = stdA F) ∧
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A t₁ = s.1 ∧
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A t₂ = s.2 := by
  classical
  have key : ∀ (A : GL (Fin 3) F) (t : SL(3, F)) (u : SL(3, F)),
      (A : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (u : Matrix (Fin 3) (Fin 3) F) →
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A t = u := by
    intro A t u htu
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
    apply Units.ext
    exact htu
  rcases h with ⟨c, φ₁, φ₂, hc, h1, h2, hind, ht₁, ht₂⟩ | ⟨ψ, w₁, w₂, hψ, h1, h2, hind, ht₁, ht₂⟩
  ·
    obtain ⟨ψ₀, h0⟩ := exists_dotProduct_eq_one hc
    let P : Matrix (Fin 3) (Fin 3) F := Matrix.of ![ψ₀, φ₁, φ₂]
    have hP : IsUnit P := by
      rw [← Matrix.linearIndependent_rows_iff_isUnit]
      have := linearIndependent_three h0 h1 h2 hind
      convert this using 1
      funext r
      fin_cases r <;> rfl
    let A : GL (Fin 3) F := hP.unit
    have hA : (A : Matrix (Fin 3) (Fin 3) F) = P := rfl
    have hAc : P *ᵥ c = ![1, 0, 0] := by
      funext r
      fin_cases r <;> simp [P, Matrix.mulVec, h0, h1, h2]
    have hrow : ∀ (r : Fin 3), vecMul (Pi.single r 1) P = ![ψ₀, φ₁, φ₂] r := by
      intro r
      funext x
      simp [P, vecMul, dotProduct, Pi.single_apply]
    have hinv : ∀ r : Fin 3, vecMul (![ψ₀, φ₁, φ₂] r) ((A⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = Pi.single r 1 := by
      intro r
      rw [← hrow r, vecMul_vecMul, ← hA, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        vecMul_one]
    have hconj : ∀ (φ : Fin 3 → F) (t : SL(3, F)), (t : Matrix (Fin 3) (Fin 3) F) =
        1 + vecMulVec c φ → (A : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          1 + vecMulVec (P *ᵥ c) (vecMul φ ((A⁻¹ : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F)) := by
      intro φ t ht
      rw [ht, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hA]
    refine ⟨A, stdC F, Or.inl rfl, key A t₁ _ ?_, key A t₂ _ ?_⟩
    · rw [hconj φ₁ t₁ ht₁, hAc, show φ₁ = ![ψ₀, φ₁, φ₂] 1 from rfl, hinv]
      simp only [stdC, up3_coe]
      ext r s
      rw [Matrix.add_apply, vecMulVec_apply]
      fin_cases r <;> fin_cases s <;> simp [upMat]
    · rw [hconj φ₂ t₂ ht₂, hAc, show φ₂ = ![ψ₀, φ₁, φ₂] 2 from rfl, hinv]
      simp only [stdC, up3_coe]
      ext r s
      rw [Matrix.add_apply, vecMulVec_apply]
      fin_cases r <;> fin_cases s <;> simp [upMat]
  ·
    obtain ⟨x₀, h0⟩ := exists_dotProduct_eq_one hψ
    have h0' : ψ ⬝ᵥ x₀ = 1 := by rw [dotProduct_comm]; exact h0
    let N : Matrix (Fin 3) (Fin 3) F := (Matrix.of ![w₁, w₂, x₀])ᵀ
    have hN : IsUnit N := by
      rw [Matrix.isUnit_transpose, ← Matrix.linearIndependent_rows_iff_isUnit]
      have h1' : w₁ ⬝ᵥ ψ = 0 := by rw [dotProduct_comm]; exact h1
      have h2' : w₂ ⬝ᵥ ψ = 0 := by rw [dotProduct_comm]; exact h2
      have := linearIndependent_three (c := ψ) (ψ₀ := x₀) h0 h1' h2' hind
      have hperm : LinearIndependent F ![w₁, w₂, x₀] := by
        have e : (![w₁, w₂, x₀] : Fin 3 → Fin 3 → F) = ![x₀, w₁, w₂] ∘
            ((finRotate 3) : Fin 3 → Fin 3) := by
          funext r
          fin_cases r <;> rfl
        rw [e]
        exact this.comp _ (finRotate 3).injective
      convert hperm using 1
      funext r
      fin_cases r <;> rfl
    let A : GL (Fin 3) F := hN.unit⁻¹
    have hAinv : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = N := by
      simp [A]
    have hcol : ∀ r : Fin 3, N *ᵥ Pi.single r 1 = ![w₁, w₂, x₀] r := by
      intro r
      funext x
      simp [N, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hAw : ∀ r : Fin 3, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![w₁, w₂, x₀] r =
        Pi.single r 1 := by
      intro r
      rw [← hcol r, Matrix.mulVec_mulVec, ← hAinv, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mulVec]
    have hψN : vecMul ψ N = ![0, 0, 1] := by
      funext r
      fin_cases r <;> simp [N, vecMul, dotProduct, Fin.sum_univ_three] <;>
        [simpa [dotProduct, Fin.sum_univ_three, mul_comm] using h1;
          simpa [dotProduct, Fin.sum_univ_three, mul_comm] using h2;
          simpa [dotProduct, Fin.sum_univ_three, mul_comm] using h0']
    have hconj : ∀ (w : Fin 3 → F) (t : SL(3, F)), (t : Matrix (Fin 3) (Fin 3) F) =
        1 + vecMulVec w ψ → (A : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          1 + vecMulVec ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ w) (vecMul ψ N) := by
      intro w t ht
      rw [ht, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hAinv]
    refine ⟨A, stdA F, Or.inr rfl, key A t₁ _ ?_, key A t₂ _ ?_⟩
    · rw [hconj w₁ t₁ ht₁, show w₁ = ![w₁, w₂, x₀] 0 from rfl, hAw, hψN]
      simp only [stdA, up3_coe]
      ext r s
      rw [Matrix.add_apply, vecMulVec_apply]
      fin_cases r <;> fin_cases s <;> simp [upMat]
    · rw [hconj w₂ t₂ ht₂, show w₂ = ![w₁, w₂, x₀] 1 from rfl, hAw, hψN]
      simp only [stdA, up3_coe]
      ext r s
      rw [Matrix.add_apply, vecMulVec_apply]
      fin_cases r <;> fin_cases s <;> simp [upMat]

end Std


section Kappa

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

omit [Fintype F] in
theorem std_fst {s : SL(3, F) × SL(3, F)} (hs : s = stdC F ∨ s = stdA F) :
    s.1 ≠ 1 ∧ s.1 * s.1 = 1 := by
  have hne : ∀ x y z : F, (x ≠ 0 ∨ z ≠ 0) → up3 x y z ≠ 1 := by
    intro x y z hxz h
    have h1 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 1 2) h
    have h2 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 1) h
    simp [up3_coe, upMat] at h1 h2
    tauto
  have h1 : up3 (0 : F) 0 0 = 1 := by
    apply Subtype.ext
    ext r s
    fin_cases r <;> fin_cases s <;> simp [up3_coe, upMat]
  have hsq : ∀ y : F, up3 0 y 0 * up3 0 y 0 = 1 ∧ up3 1 0 0 * up3 (1 : F) 0 0 = 1 ∧
      up3 0 0 1 * up3 (0 : F) 0 1 = 1 := by
    intro y
    refine ⟨?_, ?_, ?_⟩ <;> rw [up3_mul] <;> simpa [CharTwo.add_self_eq_zero] using h1
  rcases hs with rfl | rfl
  · refine ⟨hne 0 0 1 (Or.inr one_ne_zero), (hsq 0).2.2⟩
  · refine ⟨fun h => ?_, (hsq 1).1⟩
    have h1 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 2) h
    simp [stdA, up3_coe, upMat] at h1

theorem exists_double_pos {a b : Fin f → Bool} (hS : cntS a b = 0) (hH : cntH a b = 1) :
    ∃ i₀ : Fin f, (a i₀, b i₀) = (true, true) ∧ ∀ p, p ≠ i₀ → (a p, b p) = (false, false) := by
  classical
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hH
  have hmem : ∀ p, (a p = true ∧ b p = true) ↔ p = i₀ := by
    intro p
    have := congrArg (fun s : Finset (Fin f) => p ∈ s) hi₀
    simpa using this
  have hS' : ∀ p, a p = b p := by
    intro p
    by_contra hp
    have : p ∈ Finset.univ.filter fun i => a i ≠ b i := by simp [hp]
    have h0 : (Finset.univ.filter fun i => a i ≠ b i).card = 0 := hS
    rw [Finset.card_eq_zero] at h0
    rw [h0] at this
    simp at this
  refine ⟨i₀, ?_, fun p hp => ?_⟩
  · obtain ⟨h1, h2⟩ := (hmem i₀).mpr rfl
    rw [h1, h2]
  · have h1 : ¬ (a p = true ∧ b p = true) := fun h => hp ((hmem p).mp h)
    have h2 := hS' p
    cases ha : a p <;> cases hb : b p <;> simp_all

theorem four_le_rank_std (a b : Fin f → Bool) (h8 : 8 ≤ 3 ^ cntS a b * 8 ^ cntH a b)
    {s : SL(3, F) × SL(3, F)} (hs : s = stdC F ∨ s = stdA F) :
    4 ≤ (tensorRep (F := F) F a b s.1 - 1).rank := by
  obtain ⟨h1, h2⟩ := std_fst hs
  rw [rank_tensorRep_involution a b h1 h2]
  have := dim_le_two_mul_rank_tensorRep (F := F) a b
  omega

theorem five_le_codim_std (a b : Fin f → Bool)
    (hab : (cntS a b = 2 ∧ cntH a b = 0) ∨ (cntS a b = 0 ∧ cntH a b = 1))
    {s : SL(3, F) × SL(3, F)} (hs : s = stdC F ∨ s = stdA F) :
    5 ≤ Module.finrank F (TIdx f a b → F) -
      Module.finrank F (repFixedSpace (matRep (tensorRep (F := F) F a b)) {s.1, s.2}) := by
  classical
  have h8 : 8 ≤ 3 ^ cntS a b * 8 ^ cntH a b := by
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num
  have hrk := four_le_rank_std (F := F) a b h8 hs
  rcases hab with ⟨hS, hH⟩ | ⟨hS, hH⟩
  ·
    obtain ⟨i, i', hii', hsi, hsi', hrest⟩ := B42SL3.exists_two_pos hS hH
    obtain ⟨w, hw₀, c, c', hw₁⟩ := exists_vec_kron (F := F) hsi hsi' (i : ℕ) (i' : ℕ) hs
    let τ : Fin f → Bool × Bool := fun p => (a p, b p)
    let v : TIdx f a b → F := fun z => w (z i) (z i')
    have hv₀ : tensorRep (F := F) F a b s.1 *ᵥ v = v := by
      funext y
      exact (mulVec_lift_two (F := F) τ (fun p : Fin f => (p : ℕ)) hii' hrest s.1 w y).trans
        (hw₀ (y i) (y i'))
    have hv₁ : tensorRep (F := F) F a b s.2 *ᵥ v ≠ v := by
      intro h
      obtain ⟨y, hy, hy'⟩ := exists_idx_two τ hii' c c'
      have h1 := congrFun h y
      have h3 : (tensorRep (F := F) F a b s.2 *ᵥ v) y = ∑ c, ∑ c',
          locRep F (τ i).1 (τ i).2 (i : ℕ) s.2 (y i) c *
            locRep F (τ i').1 (τ i').2 (i' : ℕ) s.2 (y i') c' * w c c' :=
        mulVec_lift_two (F := F) τ (fun p : Fin f => (p : ℕ)) hii' hrest s.2 w y
      rw [h3] at h1
      apply hw₁
      have h2 : v y = w c c' := by simp only [v, hy, hy']
      rw [← h2, ← h1, hy, hy']
    have := rank_add_one_le_codim (tensorRep (F := F) F a b) hv₀ hv₁
    omega
  ·
    obtain ⟨i₀, hi₀, hrest⟩ := exists_double_pos hS hH
    let τ : Fin f → Bool × Bool := fun p => (a p, b p)
    obtain ⟨e⟩ := B42SL3.nonempty_equiv_locRep (F := F) τ (fun p : Fin f => (p : ℕ)) (i₀ := i₀)
      hrest
    have hcodim : ∀ A : Set SL(3, F),
        Module.finrank F (TIdx f a b → F) -
          Module.finrank F (repFixedSpace (matRep (tensorRep (F := F) F a b)) A) =
        Module.finrank F (Fin (locDim (τ i₀).1 (τ i₀).2) → F) -
          Module.finrank F (repFixedSpace (matRep (locRep F (τ i₀).1 (τ i₀).2 (i₀ : ℕ))) A) := by
      intro A
      show Module.finrank F (TIdx f a b → F) - Module.finrank F (repFixedSpace
        (matRep (tensorRepGen F τ (fun p : Fin f => (p : ℕ)))) A) = _
      rw [finrank_repFixedSpace_equiv e A, LinearEquiv.finrank_eq e.toLinearEquiv]
    have hloc : ∀ {ℓ : Bool × Bool}, ℓ = (true, true) → ∀ j : ℕ,
        (locRep F ℓ.1 ℓ.2 j s.1 - 1).rank + 1 ≤
          Module.finrank F (Fin (locDim ℓ.1 ℓ.2) → F) -
            Module.finrank F (repFixedSpace (matRep (locRep F ℓ.1 ℓ.2 j)) {s.1, s.2}) := by
      rintro ℓ rfl j
      obtain ⟨w, hw₀, hw₁⟩ := exists_vec_adj (F := F) j hs
      exact rank_add_one_le_codim (adjRep F j) hw₀ hw₁
    have h1 : (locRep F (τ i₀).1 (τ i₀).2 (i₀ : ℕ) s.1 - 1).rank + 1 ≤
        Module.finrank F (Fin (locDim (τ i₀).1 (τ i₀).2) → F) -
          Module.finrank F (repFixedSpace (matRep (locRep F (τ i₀).1 (τ i₀).2 (i₀ : ℕ)))
            {s.1, s.2}) := hloc hi₀ (i₀ : ℕ)
    have h2 : (tensorRep (F := F) F a b s.1 - 1).rank =
        (locRep F (τ i₀).1 (τ i₀).2 (i₀ : ℕ) s.1 - 1).rank := by
      have e1 := CFSG.QuasithinUnique.Setup.X7b.fixedCodim_matRep (tensorRep (F := F) F a b) s.1
      have e2 := CFSG.QuasithinUnique.Setup.X7b.fixedCodim_matRep
        (locRep F (τ i₀).1 (τ i₀).2 (i₀ : ℕ)) s.1
      rw [← e1, ← e2]
      exact hcodim {s.1}
    rw [hcodim]
    omega

theorem five_le_codim_pair (a b : Fin f → Bool)
    (hab : (cntS a b = 2 ∧ cntH a b = 0) ∨ (cntS a b = 0 ∧ cntH a b = 1))
    {t₁ t₂ : SL(3, F)} (hpair : IsRootPair t₁ t₂) :
    5 ≤ Module.finrank F (TIdx f a b → F) -
      Module.finrank F (repFixedSpace (matRep (tensorRep (F := F) F a b)) {t₁, t₂}) := by
  classical
  obtain ⟨A, s, hs, h₁, h₂⟩ := exists_conj_std hpair
  have hiso := tensorRep_comp_conj (F := F) F A a b
  obtain ⟨e⟩ := hiso.equiv
  have h1 := finrank_repFixedSpace_equiv e {t₁, t₂}
  rw [repFixedSpace_comp, Set.image_pair, MulEquiv.coe_toMonoidHom, h₁, h₂] at h1
  rw [← h1]
  exact five_le_codim_std a b hab hs

end Kappa

section Sum

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

omit [CharP F 2] [Fintype F] in
theorem codim_ker_map_le {K L : Type} [Field K] [Field L] (φ : K →+* L) {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq n] (D : Matrix m n K) :
    Fintype.card n - Module.finrank L (LinearMap.ker (Matrix.mulVecLin (D.map φ))) ≤
      Fintype.card n - Module.finrank K (LinearMap.ker (Matrix.mulVecLin D)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (D.map φ))
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin D)
  have hr := CFSG.QuasithinUnique.Setup.X7b.rank_map_ringHom_le φ D
  rw [Matrix.rank, Matrix.rank] at hr
  rw [Module.finrank_fintype_fun_eq_card] at h1 h2
  omega

omit [Fintype F] in
theorem codimPF_le {n : ℕ} (ρ : Representation (ZMod 2) SL(3, F) U)
    (bas : Module.Basis (Fin n) (ZMod 2) U) (t₁ t₂ : SL(3, F)) :
    Module.finrank F (Fin n → F) - Module.finrank F (repFixedSpace
        (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas))) {t₁, t₂}) ≤
      Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) (repFixedSpace ρ {t₁, t₂}) := by
  classical
  set φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hφ
  set ρ₀ := toMatRep ρ bas with hρ₀
  let D : Matrix (Fin n ⊕ Fin n) (Fin n) (ZMod 2) := Matrix.fromRows (ρ₀ t₁ - 1) (ρ₀ t₂ - 1)
  have hkerF : repFixedSpace (matRep (matMap φ ρ₀)) {t₁, t₂} =
      LinearMap.ker (Matrix.mulVecLin (D.map φ)) := by
    ext v
    simp only [mem_repFixedSpace, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq, matRep_apply, matMap_apply, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨h1, h2⟩
      funext r
      rcases r with r | r
      · have := congrFun h1 r
        simp only [D, Matrix.mulVec, dotProduct, Matrix.fromRows_apply_inl,
          Matrix.map_apply, Matrix.sub_apply, map_sub, Pi.zero_apply] at this ⊢
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        convert this using 1
        simp [Matrix.one_apply, apply_ite φ]
      · have := congrFun h2 r
        simp only [D, Matrix.mulVec, dotProduct, Matrix.fromRows_apply_inr,
          Matrix.map_apply, Matrix.sub_apply, map_sub, Pi.zero_apply] at this ⊢
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        convert this using 1
        simp [Matrix.one_apply, apply_ite φ]
    · intro h
      refine ⟨funext fun r => ?_, funext fun r => ?_⟩
      · have := congrFun h (Sum.inl r)
        simp only [D, Matrix.mulVec, dotProduct, Matrix.fromRows_apply_inl,
          Matrix.map_apply, Matrix.sub_apply, map_sub, Pi.zero_apply, sub_mul,
          Finset.sum_sub_distrib, sub_eq_zero] at this ⊢
        rw [this]
        simp [Matrix.one_apply, apply_ite φ]
      · have := congrFun h (Sum.inr r)
        simp only [D, Matrix.mulVec, dotProduct, Matrix.fromRows_apply_inr,
          Matrix.map_apply, Matrix.sub_apply, map_sub, Pi.zero_apply, sub_mul,
          Finset.sum_sub_distrib, sub_eq_zero] at this ⊢
        rw [this]
        simp [Matrix.one_apply, apply_ite φ]
  have hker2 : (repFixedSpace ρ {t₁, t₂}).map bas.equivFun.toLinearMap =
      LinearMap.ker (Matrix.mulVecLin D) := by
    ext v
    simp only [Submodule.mem_map, mem_repFixedSpace, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    have hmat : ∀ (g : SL(3, F)) (u : U),
        bas.equivFun (ρ g u) = ρ₀ g *ᵥ bas.equivFun u := by
      intro g u
      have := Representation.IntertwiningMap.isIntertwining ρ (matRep (toMatRep ρ bas))
        (CFSG.QuasithinUnique.Setup.X7b.matRepEquiv ρ bas).toIntertwiningMap g u
      exact this
    constructor
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      funext r
      rcases r with r | r
      · simp only [D, Matrix.fromRows_mulVec, Sum.elim_inl, Matrix.sub_mulVec, Matrix.one_mulVec,
          Pi.sub_apply, Pi.zero_apply, LinearEquiv.coe_coe]
        rw [← hmat, h1, sub_self]
      · simp only [D, Matrix.fromRows_mulVec, Sum.elim_inr, Matrix.sub_mulVec, Matrix.one_mulVec,
          Pi.sub_apply, Pi.zero_apply, LinearEquiv.coe_coe]
        rw [← hmat, h2, sub_self]
    · intro h
      refine ⟨bas.equivFun.symm v, ⟨?_, ?_⟩, bas.equivFun.apply_symm_apply v⟩
      · apply bas.equivFun.injective
        rw [hmat, LinearEquiv.apply_symm_apply]
        have := congrFun h
        simp only [D, Matrix.fromRows_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] at this
        funext r
        have hr := this (Sum.inl r)
        simp only [Sum.elim_inl, Pi.sub_apply, Pi.zero_apply] at hr
        exact sub_eq_zero.mp hr
      · apply bas.equivFun.injective
        rw [hmat, LinearEquiv.apply_symm_apply]
        have := congrFun h
        simp only [D, Matrix.fromRows_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] at this
        funext r
        have hr := this (Sum.inr r)
        simp only [Sum.elim_inr, Pi.sub_apply, Pi.zero_apply] at hr
        exact sub_eq_zero.mp hr
  have hdimU : Module.finrank (ZMod 2) U = n := by
    rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]
  have hdim2 : Module.finrank (ZMod 2) (repFixedSpace ρ {t₁, t₂}) =
      Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin D)) := by
    rw [← hker2, LinearEquiv.finrank_map_eq]
  have hmain := codim_ker_map_le φ D
  rw [Fintype.card_fin] at hmain
  rw [hkerF, hdim2, hdimU, Module.finrank_fin_fun]
  exact hmain

theorem five_mul_card_le_codim (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {n : ℕ}
    (ρ : Representation (ZMod 2) SL(3, F) U) (bas : Module.Basis (Fin n) (ZMod 2) U)
    (O : Finset ((Fin f → Bool) × (Fin f → Bool)))
    (hO : ∀ c ∈ O, 0 < repMultiplicity
      (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas)))
      (matRep (tensorRep (F := F) F c.1 c.2)))
    (htype : ∀ c ∈ O, (cntS c.1 c.2 = 2 ∧ cntH c.1 c.2 = 0) ∨
      (cntS c.1 c.2 = 0 ∧ cntH c.1 c.2 = 1))
    {t₁ t₂ : SL(3, F)} (hpair : IsRootPair t₁ t₂) :
    5 * O.card ≤
      Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) (repFixedSpace ρ {t₁, t₂}) := by
  classical
  set PF := matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas) with hPF
  have key := CFSG.QuasithinUnique.Setup.X7b.sum_repMultiplicity_mul_fixedCodim_le (k := F)
    (matRep PF) {t₁, t₂} (ι := ↥O) (fun t => TIdx f t.1.1 t.1.2 → F)
    (fun t => matRep (tensorRep (F := F) F t.1.1 t.1.2))
    (fun t t' h => Subtype.ext (Prod.ext
      ((tensorRep_absolutely_irreducible_and_distinct F hF hf).2 _ _ _ _ h).1
      ((tensorRep_absolutely_irreducible_and_distinct F hF hf).2 _ _ _ _ h).2))
  refine le_trans ?_ (key.trans (codimPF_le ρ bas t₁ t₂))
  calc 5 * O.card = ∑ _t : ↥O, 5 := by simp [mul_comm]
    _ ≤ _ := by
      refine Finset.sum_le_sum fun t _ => ?_
      have h5 := five_le_codim_pair (F := F) t.1.1 t.1.2 (htype t.1 t.2) hpair
      have hm := hO t.1 t.2
      calc 5 ≤ Module.finrank F (TIdx f t.1.1 t.1.2 → F) -
            Module.finrank F (repFixedSpace (matRep (tensorRep (F := F) F t.1.1 t.1.2))
              {t₁, t₂}) := h5
        _ ≤ _ := Nat.le_mul_of_pos_left _ hm

end Sum

end B45SL3

end CFSG.Quasithin
