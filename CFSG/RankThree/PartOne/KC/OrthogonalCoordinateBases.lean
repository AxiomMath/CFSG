module

public import CFSG.RankThree.PartOne.KC.OrthogonalTraceModels
public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module

section Paired

variable {K E U₁ U₂ : Type*} [Field K] [Field E] [Algebra K E] [Finite E]
  [AddCommGroup U₁] [Module K U₁] [Module E U₁] [IsScalarTower K E U₁] [Module.Finite E U₁]
  [AddCommGroup U₂] [Module K U₂] [Module E U₂] [IsScalarTower K E U₂] [Module.Finite E U₂]

theorem exists_paired_trace_coordinates (β : U₁ →ₗ[K] U₂ →ₗ[K] K)
    (hβ : ∀ (a : E) (u : U₁) (w : U₂), β (a • u) w = β u (a • w))
    (hl : ∀ u, (∀ w, β u w = 0) → u = 0) (hr : ∀ w, (∀ u, β u w = 0) → w = 0) :
    ∃ (ι₁ : (Fin (finrank E U₁) → E) ≃ₗ[E] U₁) (ι₂ : (Fin (finrank E U₁) → E) ≃ₗ[E] U₂),
      ∀ a b, β (ι₁ a) (ι₂ b) = Algebra.trace K E (∑ i, a i * b i) := by
  classical
  have : Module.Finite K U₁ := Module.Finite.trans E U₁
  have : Module.Finite K U₂ := Module.Finite.trans E U₂
  set m := finrank E U₁ with hm
  let b₁ : Basis (Fin m) E U₁ := Module.finBasis E U₁
  let φ : Fin m → (U₁ →ₗ[K] K) := fun j =>
    (Algebra.trace K E).comp ((b₁.coord j).restrictScalars K)
  have hφ : ∀ j u, φ j u = Algebra.trace K E (b₁.repr u j) := fun j u => rfl
  have hinj₂ : Function.Injective (β.flip : U₂ →ₗ[K] Module.Dual K U₁) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact hr w fun u => by simpa using LinearMap.congr_fun hw u
  have hinj₁ : Function.Injective (β : U₁ →ₗ[K] Module.Dual K U₂) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    exact hl u fun w => by simpa using LinearMap.congr_fun hu w
  have hdim : finrank K U₁ = finrank K U₂ := by
    refine le_antisymm ?_ ?_
    · have := LinearMap.finrank_le_finrank_of_injective hinj₁
      rwa [Subspace.dual_finrank_eq] at this
    · have := LinearMap.finrank_le_finrank_of_injective hinj₂
      rwa [Subspace.dual_finrank_eq] at this
  have hsurj : Function.Surjective (β.flip : U₂ →ₗ[K] Module.Dual K U₁) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq]; exact hdim.symm)).mp hinj₂
  choose w hw using fun j => hsurj (φ j)
  have hwβ : ∀ j u, β u (w j) = φ j u := fun j u => by
    simpa using LinearMap.congr_fun (hw j) u
  have hdimE : finrank E U₂ = m := by
    have h1 := Module.finrank_mul_finrank K E U₁
    have h2 := Module.finrank_mul_finrank K E U₂
    have hpos : 0 < finrank K E := Module.finrank_pos
    rw [hdim] at h1
    exact (Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)).symm
  have hbal : ∀ (a : E) (i j : Fin m) (c : E), β (c • b₁ i) (a • w j) =
      if i = j then Algebra.trace K E (a * c) else 0 := by
    intro a i j c
    rw [← hβ, hwβ, hφ, smul_smul, map_smul, Basis.repr_self]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hli : LinearIndependent E w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    refine eq_zero_of_trace_mul_eq_zero K E fun c => ?_
    have h1 := congrArg (β (c • b₁ i)) hg
    rw [map_sum, map_zero] at h1
    simp only [hbal, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h1
    exact h1
  have hcard : Fintype.card (Fin m) = finrank E U₂ := by rw [Fintype.card_fin, hdimE]
  let b₂ : Basis (Fin m) E U₂ := basisOfLinearIndependentOfCardEqFinrank' w hli hcard
  have hb₂ : ∀ j, b₂ j = w j := fun j => by simp [b₂]
  refine ⟨b₁.equivFun.symm, b₂.equivFun.symm, fun a b => ?_⟩
  rw [Basis.equivFun_symm_apply, Basis.equivFun_symm_apply]
  simp only [map_sum, LinearMap.sum_apply]
  have h2 : ∀ i j, β (a i • b₁ i) (b j • b₂ j) =
      if i = j then Algebra.trace K E (b j * a i) else 0 := fun i j => by
    rw [hb₂]; exact hbal (b j) i j (a i)
  simp only [h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

end Paired

section TraceDual

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Finite E]

theorem exists_unique_trace_dual (f : E →ₗ[K] K) :
    ∃! e : E, ∀ c, Algebra.trace K E (e * c) = f c := by
  obtain ⟨e, he⟩ := ((Algebra.traceForm K E).toDual (traceForm_nondegenerate K E)).surjective f
  refine ⟨e, fun c => ?_, fun e' he' => ?_⟩
  · have := LinearMap.congr_fun he c
    simpa [LinearMap.BilinForm.toDual_def] using this
  · have h1 : ∀ c, Algebra.trace K E (e * c) = f c := fun c => by
      have := LinearMap.congr_fun he c
      simpa [LinearMap.BilinForm.toDual_def] using this
    refine sub_eq_zero.mp (eq_zero_of_trace_mul_eq_zero K E fun c => ?_)
    rw [sub_mul, map_sub, he', h1, sub_self]

theorem eq_of_trace_mul_eq {e e' : E}
    (h : ∀ c, Algebra.trace K E (e * c) = Algebra.trace K E (e' * c)) : e = e' := by
  refine sub_eq_zero.mp (eq_zero_of_trace_mul_eq_zero K E fun c => ?_)
  rw [sub_mul, map_sub, h, sub_self]

end TraceDual

section Hermitian

variable {K : Type*} (E : Type*) {U : Type*} [Field K] [Field E] [Algebra K E] [Finite E]
  [AddCommGroup U] [Module K U] [Module E U] [IsScalarTower K E U]
  (β : U →ₗ[K] U →ₗ[K] K)

@[expose] noncomputable def hermFunctional (u w : U) : E →ₗ[K] K :=
  (β u).comp ((LinearMap.toSpanSingleton E U w).restrictScalars K)

omit [Finite E] in
theorem hermFunctional_apply (u w : U) (c : E) : hermFunctional E β u w c = β u (c • w) := rfl

@[expose] noncomputable def hermForm (u w : U) : E :=
  Classical.choose (exists_unique_trace_dual (hermFunctional E β u w)).exists

theorem trace_hermForm_mul (u w : U) (c : E) :
    Algebra.trace K E (hermForm E β u w * c) = β u (c • w) :=
  Classical.choose_spec (exists_unique_trace_dual (hermFunctional E β u w)).exists c

theorem hermForm_eq_of_trace {u w : U} {e : E}
    (h : ∀ c, Algebra.trace K E (e * c) = β u (c • w)) : hermForm E β u w = e :=
  eq_of_trace_mul_eq fun c => by rw [trace_hermForm_mul, h]

theorem trace_hermForm (u w : U) : Algebra.trace K E (hermForm E β u w) = β u w := by
  simpa using trace_hermForm_mul E β u w 1

theorem hermForm_add_right (u w w' : U) :
    hermForm E β u (w + w') = hermForm E β u w + hermForm E β u w' :=
  hermForm_eq_of_trace E β fun c => by
    rw [add_mul, map_add, trace_hermForm_mul, trace_hermForm_mul, smul_add, map_add]

theorem hermForm_add_left (u u' w : U) :
    hermForm E β (u + u') w = hermForm E β u w + hermForm E β u' w :=
  hermForm_eq_of_trace E β fun c => by
    rw [add_mul, map_add, trace_hermForm_mul, trace_hermForm_mul, map_add]; rfl

theorem hermForm_smul_right (a : E) (u w : U) :
    hermForm E β u (a • w) = a * hermForm E β u w :=
  hermForm_eq_of_trace E β fun c => by
    have : a * hermForm E β u w * c = hermForm E β u w * (a * c) := by ring
    rw [this, trace_hermForm_mul, smul_smul, mul_comm]

theorem hermForm_zero_right (u : U) : hermForm E β u 0 = 0 := by
  have := hermForm_smul_right E β (0 : E) u 0
  simpa using this

section Sesquilinear

variable {E β} (σ : E ≃ₐ[K] E)

theorem hermForm_smul_left (hbal : ∀ (a : E) u w, β (a • u) w = β u (σ a • w)) (a : E) (u w : U) :
    hermForm E β (a • u) w = σ a * hermForm E β u w :=
  hermForm_eq_of_trace E β fun c => by
    have : σ a * hermForm E β u w * c = hermForm E β u w * (σ a * c) := by ring
    rw [this, trace_hermForm_mul, hbal, smul_smul]

theorem hermForm_symm (hσσ : ∀ z, σ (σ z) = z) (hsymm : ∀ u w, β u w = β w u)
    (hbal : ∀ (a : E) u w, β (a • u) w = β u (σ a • w)) (u w : U) :
    hermForm E β w u = σ (hermForm E β u w) :=
  hermForm_eq_of_trace E β fun c => by
    have h1 : β w (c • u) = Algebra.trace K E (hermForm E β u w * σ c) := by
      rw [hsymm, hbal, ← trace_hermForm_mul E β u w (σ c)]
    rw [h1, ← Algebra.trace_eq_of_algEquiv σ (hermForm E β u w * σ c), map_mul σ, hσσ]

theorem eq_zero_of_hermForm_eq_zero (hnd : ∀ u, (∀ w, β u w = 0) → u = 0) {u : U}
    (h : ∀ w, hermForm E β u w = 0) : u = 0 :=
  hnd u fun w => by rw [← trace_hermForm E β u w, h, map_zero]

theorem hermForm_zero_left (u : U) : hermForm E β 0 u = 0 := by
  have := hermForm_add_left E β 0 0 u
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem hermForm_sum_right {ι : Type*} (s : Finset ι) (u : U) (w : ι → U) :
    hermForm E β u (∑ i ∈ s, w i) = ∑ i ∈ s, hermForm E β u (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermForm_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermForm_add_right, ih]

theorem hermForm_sum_left {ι : Type*} (s : Finset ι) (u : ι → U) (w : U) :
    hermForm E β (∑ i ∈ s, u i) w = ∑ i ∈ s, hermForm E β (u i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermForm_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermForm_add_left, ih]

end Sesquilinear

end Hermitian

section Matrix

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

theorem herm_mulVec_left {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) F) (a y : Fin n → F) :
    herm σ (M.mulVec a) y = herm σ a ((conjTr σ M).mulVec y) := by
  simp only [herm, Matrix.mulVec, dotProduct, conjTr, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Matrix

section Coordinates

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} {E : Type*} {U : Type*} [Field K] [Field E] [Algebra K E] [Finite E]
  [AddCommGroup U] [Module K U] [Module E U] [IsScalarTower K E U] [Module.Finite E U]

theorem exists_hermitian_trace_coordinates (β : U →ₗ[K] U →ₗ[K] K) (σ : E ≃ₐ[K] E)
    (hσ : IsUnitaryInvolution σ.toRingEquiv) (hsymm : ∀ u w, β u w = β w u)
    (hbal : ∀ (a : E) (u w : U), β (a • u) w = β u (σ a • w))
    (hnd : ∀ u, (∀ w, β u w = 0) → u = 0) :
    ∃ ι : (Fin (finrank E U) → E) ≃ₗ[E] U,
      ∀ a b, β (ι a) (ι b) = Algebra.trace K E (∑ i, σ (a i) * b i) := by
  classical
  set m := finrank E U with hm
  have hσσ : ∀ z, σ (σ z) = z := hσ.invol
  let b : Basis (Fin m) E U := Module.finBasis E U
  let G : Matrix (Fin m) (Fin m) E := Matrix.of fun i j => hermForm E β (b i) (b j)
  have hcoord : ∀ x y : Fin m → E,
      hermForm E β (b.equivFun.symm x) (b.equivFun.symm y) = herm σ.toRingEquiv x (G.mulVec y) := by
    intro x y
    rw [Basis.equivFun_symm_apply, Basis.equivFun_symm_apply, hermForm_sum_left, herm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hermForm_sum_right, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hermForm_smul_left σ hbal, hermForm_smul_right]
    have hσ' : σ.toRingEquiv (x i) = σ (x i) := rfl
    rw [hσ']
    simp only [G, Matrix.of_apply]
    ring
  have hG : conjTr σ.toRingEquiv G = G := by
    ext i j
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, G, Matrix.of_apply]
    exact (hermForm_symm (β := β) σ hσσ hsymm hbal (b j) (b i)).symm
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine hv0 (b.equivFun.symm.map_eq_zero_iff.mp
      (eq_zero_of_hermForm_eq_zero (E := E) hnd fun w => ?_))
    have hw : w = b.equivFun.symm (b.equivFun w) := (b.equivFun.symm_apply_apply w).symm
    rw [hermForm_symm (β := β) σ hσσ hsymm hbal, hw, hcoord, hGv]
    simp [herm]
  obtain ⟨P, hP⟩ :=
    CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution hσ hG hdet
  have hPi : (P : Matrix (Fin m) (Fin m) E) * ((P⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hiP : ((P⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) * (P : Matrix (Fin m) (Fin m) E) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let T : (Fin m → E) ≃ₗ[E] (Fin m → E) :=
    LinearEquiv.ofLinearMap (Matrix.mulVecLin (P : Matrix (Fin m) (Fin m) E))
      (Matrix.mulVecLin ((P⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E))
      (LinearMap.ext fun v => by
        simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.id_apply,
          Matrix.mulVec_mulVec, hPi, Matrix.one_mulVec])
      (LinearMap.ext fun v => by
        simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.id_apply,
          Matrix.mulVec_mulVec, hiP, Matrix.one_mulVec])
  have hT : ∀ v, T v = (P : Matrix (Fin m) (Fin m) E).mulVec v := fun v => rfl
  refine ⟨T.trans b.equivFun.symm, fun x y => ?_⟩
  rw [← trace_hermForm E β]
  change Algebra.trace K E (hermForm E β (b.equivFun.symm (T x)) (b.equivFun.symm (T y))) = _
  rw [hcoord, hT, hT, herm_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP,
    Matrix.one_mulVec]
  rfl

end Coordinates

end CFSG.RankThree.PartOne.KCOrthogonal
