module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBOrth

variable {K : Type} [Field K]

section Levi

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

@[expose] def blockOneMat :
    Matrix ι' ι' K →* Matrix (ι' ⊕ (Fin 1 ⊕ Fin 1)) (ι' ⊕ (Fin 1 ⊕ Fin 1)) K where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by
    rw [Matrix.fromBlocks_multiply]
    simp

@[expose] noncomputable def embHom (e : ι ≃ ι' ⊕ (Fin 1 ⊕ Fin 1)) : GL ι' K →* GL ι K :=
  Units.map ((Matrix.reindexAlgEquiv K K e.symm).toAlgHom.toRingHom.toMonoidHom.comp blockOneMat)

variable (e : ι ≃ ι' ⊕ (Fin 1 ⊕ Fin 1))

omit [DecidableEq ι] [DecidableEq ι'] in
theorem reindex_mul (A B : Matrix ι ι K) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B := by
  simp

theorem coe_embHom (h : GL ι' K) :
    ((embHom e h : GL ι K) : Matrix ι ι K) =
      Matrix.reindex e.symm e.symm (Matrix.fromBlocks (h : Matrix ι' ι' K) 0 0 1) :=
  rfl

theorem reindex_embHom (h : GL ι' K) :
    Matrix.reindex e e ((embHom e h : GL ι K) : Matrix ι ι K) =
      Matrix.fromBlocks (h : Matrix ι' ι' K) 0 0 1 := by
  rw [coe_embHom]
  ext z w
  simp

theorem embHom_injective : Function.Injective (embHom (K := K) e) := by
  intro h h' hh
  apply Units.ext
  have := congrArg (fun g : GL ι K => (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₁₁) hh
  simp only [reindex_embHom, Matrix.toBlocks_fromBlocks₁₁] at this
  exact this

variable {e} {Q : (ι → K) → K} {Q' : (ι' → K) → K}

omit [DecidableEq ι] [DecidableEq ι'] in
theorem mulVec_reindex (A : Matrix ι ι K) (v : ι → K) (z : ι' ⊕ (Fin 1 ⊕ Fin 1)) :
    (A *ᵥ v) (e.symm z) = (Matrix.reindex e e A *ᵥ (v ∘ e.symm)) z := by
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Function.comp_apply]
  exact (Equiv.sum_comp e.symm _).symm

theorem embHom_isometry
    (hQ : ∀ v : ι → K, Q v = Q' (fun x => v (e.symm (Sum.inl x))) +
      v (e.symm (Sum.inr (Sum.inl 0))) * v (e.symm (Sum.inr (Sum.inr 0))))
    {h : GL ι' K} (hh : ∀ w, Q' ((h : Matrix ι' ι' K) *ᵥ w) = Q' w) (v : ι → K) :
    Q ((embHom e h : Matrix ι ι K) *ᵥ v) = Q v := by
  rw [hQ, hQ]
  have h1 : (fun x => ((embHom e h : Matrix ι ι K) *ᵥ v) (e.symm (Sum.inl x))) =
      (h : Matrix ι' ι' K) *ᵥ fun x => v (e.symm (Sum.inl x)) := by
    funext x
    rw [mulVec_reindex, reindex_embHom, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inl, Matrix.zero_mulVec, add_zero]
    rfl
  have h2 : ∀ a,
      ((embHom e h : Matrix ι ι K) *ᵥ v) (e.symm (Sum.inr a)) = v (e.symm (Sum.inr a)) := by
    intro a
    rw [mulVec_reindex, reindex_embHom, Matrix.fromBlocks_mulVec]
    simp
  rw [h1, h2, h2, hh]

theorem map_embHom_orth_le
    (hQ : ∀ v : ι → K, Q v = Q' (fun x => v (e.symm (Sum.inl x))) +
      v (e.symm (Sum.inr (Sum.inl 0))) * v (e.symm (Sum.inr (Sum.inr 0)))) :
    (LargeEvenOrthGroup Q').map (embHom e) ≤ LargeEvenOrthGroup Q := by
  rintro _ ⟨h, hh, rfl⟩
  exact TableBSymp.mem_orthGroup_of_isometry (embHom_isometry hQ (isometry_of_mem_orthGroup hh))

theorem map_embHom_omega_le
    (hQ : ∀ v : ι → K, Q v = Q' (fun x => v (e.symm (Sum.inl x))) +
      v (e.symm (Sum.inr (Sum.inl 0))) * v (e.symm (Sum.inr (Sum.inr 0)))) :
    (LargeEvenOmega Q').map (embHom e) ≤ LargeEvenOmega Q := by
  rw [largeEvenOmega_def, largeEvenOmega_def, Subgroup.map_commutator]
  exact Subgroup.commutator_mono (map_embHom_orth_le hQ) (map_embHom_orth_le hQ)

end Levi

section Centralizer

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {e : ι ≃ ι' ⊕ (Fin 1 ⊕ Fin 1)} {δ : ι → Kˣ} {ζ : Kˣ}

structure IsPairTorus (e : ι ≃ ι' ⊕ (Fin 1 ⊕ Fin 1)) (δ : ι → Kˣ) (ζ : Kˣ) : Prop where
  rest : ∀ x, δ (e.symm (Sum.inl x)) = 1
  left : δ (e.symm (Sum.inr (Sum.inl 0))) = ζ
  right : δ (e.symm (Sum.inr (Sum.inr 0))) = ζ⁻¹
  sq_ne_one : ζ * ζ ≠ 1

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
theorem IsPairTorus.ne_one (h : IsPairTorus e δ ζ) : ζ ≠ 1 := by
  rintro rfl
  exact h.sq_ne_one (mul_one 1)

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
theorem IsPairTorus.ne (h : IsPairTorus e δ ζ) (a : Fin 1 ⊕ Fin 1)
    (z : ι' ⊕ (Fin 1 ⊕ Fin 1)) (hz : z ≠ Sum.inr a) :
    (δ (e.symm z) : K) ≠ δ (e.symm (Sum.inr a)) := by
  have hval : ∀ z : ι' ⊕ (Fin 1 ⊕ Fin 1),
      δ (e.symm z) = Sum.elim (fun _ => 1) (Sum.elim (fun _ => ζ) (fun _ => ζ⁻¹)) z := by
    rintro (x | i | i)
    · exact h.rest x
    · rw [Fin.fin_one_eq_zero i]
      exact h.left
    · rw [Fin.fin_one_eq_zero i]
      exact h.right
  have h1 : ζ ≠ 1 := h.ne_one
  have h2 : ζ⁻¹ ≠ 1 := inv_ne_one.mpr h1
  have h3 : ζ ≠ ζ⁻¹ := fun h' => h.sq_ne_one (by nth_rewrite 2 [h']; exact mul_inv_cancel ζ)
  intro hK
  have hU : δ (e.symm z) = δ (e.symm (Sum.inr a)) := Units.ext hK
  rw [hval, hval] at hU
  rcases z with x | i | i <;> rcases a with j | j <;>
    simp only [Sum.elim_inl, Sum.elim_inr] at hU
  · exact h1 hU.symm
  · exact h2 hU.symm
  · exact hz (by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j])
  · exact h3 hU
  · exact h3 hU.symm
  · exact hz (by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j])

omit [Fintype ι'] [DecidableEq ι'] in
theorem IsPairTorus.reindex_eq (h : IsPairTorus e δ ζ) {g : GL ι K}
    (hg : g ∈ Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K))) :
    Matrix.reindex e e (g : Matrix ι ι K) =
      Matrix.fromBlocks (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₁₁ 0 0
        (Matrix.diagonal fun a =>
          (g : Matrix ι ι K) (e.symm (Sum.inr a)) (e.symm (Sum.inr a))) := by
  have hm := commute_diagGL_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hz : ∀ z w, (δ (e.symm z) : K) ≠ δ (e.symm w) →
      (g : Matrix ι ι K) (e.symm z) (e.symm w) = 0 :=
    fun z w hzw => eq_zero_of_commute_diagonal hm hzw
  ext z w
  rcases z with x | a <;> rcases w with y | b
  · rfl
  · exact hz _ _ (h.ne b (Sum.inl x) Sum.inl_ne_inr)
  · exact hz _ _ (Ne.symm (h.ne a (Sum.inl y) Sum.inl_ne_inr))
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂,
      Matrix.diagonal_apply]
    split_ifs with hab
    · subst hab
      rfl
    · exact hz _ _ (h.ne b (Sum.inr a) (fun h' => hab (Sum.inr_injective h')))

omit [DecidableEq ι'] in
theorem IsPairTorus.toBlocks_mul (h : IsPairTorus e δ ζ) {g g' : GL ι K}
    (hg : g ∈ Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K)))
    (hg' : g' ∈ Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K))) :
    (Matrix.reindex e e ((g * g' : GL ι K) : Matrix ι ι K)).toBlocks₁₁ =
        (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₁₁ *
          (Matrix.reindex e e (g' : Matrix ι ι K)).toBlocks₁₁ ∧
      (Matrix.reindex e e ((g * g' : GL ι K) : Matrix ι ι K)).toBlocks₂₂ =
        (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₂₂ *
          (Matrix.reindex e e (g' : Matrix ι ι K)).toBlocks₂₂ := by
  rw [Units.val_mul, reindex_mul, h.reindex_eq hg, h.reindex_eq hg', Matrix.fromBlocks_multiply]
  simp

omit [Fintype ι'] in
theorem toBlocks₁₁_one' :
    (1 : Matrix (ι' ⊕ (Fin 1 ⊕ Fin 1)) (ι' ⊕ (Fin 1 ⊕ Fin 1)) K).toBlocks₁₁ = 1 := by
  rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

@[expose] noncomputable def IsPairTorus.resGL (h : IsPairTorus e δ ζ) :
    Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K)) →* GL ι' K where
  toFun g :=
    { val := (Matrix.reindex e e ((g : GL ι K) : Matrix ι ι K)).toBlocks₁₁
      inv :=
        (Matrix.reindex e e (((g⁻¹ : Subgroup.centralizer _) : GL ι K) : Matrix ι ι K)).toBlocks₁₁
      val_inv := by
        rw [← (h.toBlocks_mul g.2 (g⁻¹).2).1, ← Subgroup.coe_mul, mul_inv_cancel]
        simp only [Subgroup.coe_one, Units.val_one, Matrix.reindex_apply,
          Matrix.submatrix_one_equiv]
        exact toBlocks₁₁_one'
      inv_val := by
        rw [← (h.toBlocks_mul (g⁻¹).2 g.2).1, ← Subgroup.coe_mul, inv_mul_cancel]
        simp only [Subgroup.coe_one, Units.val_one, Matrix.reindex_apply,
          Matrix.submatrix_one_equiv]
        exact toBlocks₁₁_one' }
  map_one' := by
    apply Units.ext
    simp only [OneMemClass.coe_one, Units.val_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
    exact toBlocks₁₁_one'
  map_mul' g g' := by
    apply Units.ext
    exact (h.toBlocks_mul g.2 g'.2).1

theorem IsPairTorus.coe_resGL (h : IsPairTorus e δ ζ)
    (g : Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K))) :
    ((h.resGL g : GL ι' K) : Matrix ι' ι' K) =
      (Matrix.reindex e e ((g : GL ι K) : Matrix ι ι K)).toBlocks₁₁ :=
  rfl


omit [Fintype ι'] [DecidableEq ι'] in
theorem IsPairTorus.reindex_eq' (h : IsPairTorus e δ ζ) {g : GL ι K}
    (hg : g ∈ Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K))) :
    Matrix.reindex e e (g : Matrix ι ι K) =
      Matrix.fromBlocks (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₁₁ 0 0
        (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₂₂ := by
  have h12 : (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₁₂ = 0 := by
    rw [h.reindex_eq hg, Matrix.toBlocks_fromBlocks₁₂]
  have h21 : (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₂₁ = 0 := by
    rw [h.reindex_eq hg, Matrix.toBlocks_fromBlocks₂₁]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex e e (g : Matrix ι ι K)), h12, h21]

omit [Fintype ι'] [DecidableEq ι'] in
theorem IsPairTorus.toBlocks₂₂_commute (h : IsPairTorus e δ ζ) {g g' : GL ι K}
    (hg : g ∈ Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K)))
    (hg' : g' ∈ Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K))) :
    (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₂₂ *
        (Matrix.reindex e e (g' : Matrix ι ι K)).toBlocks₂₂ =
      (Matrix.reindex e e (g' : Matrix ι ι K)).toBlocks₂₂ *
        (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₂₂ := by
  rw [h.reindex_eq hg, h.reindex_eq hg', Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₂₂,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

omit [Fintype ι'] in
theorem toBlocks₂₂_one' :
    (1 : Matrix (ι' ⊕ (Fin 1 ⊕ Fin 1)) (ι' ⊕ (Fin 1 ⊕ Fin 1)) K).toBlocks₂₂ = 1 := by
  rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]

theorem IsPairTorus.commutator_eq (h : IsPairTorus e δ ζ)
    (g g' : Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K))) :
    ((g * g' * g⁻¹ * g'⁻¹ : Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K))) : GL ι K) =
      embHom e (h.resGL g * h.resGL g' * (h.resGL g)⁻¹ * (h.resGL g')⁻¹) := by
  set D : Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K)) →
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K := fun x =>
    (Matrix.reindex e e ((x : GL ι K) : Matrix ι ι K)).toBlocks₂₂ with hD
  have hDmul : ∀ x y, D (x * y) = D x * D y := fun x y => (h.toBlocks_mul x.2 y.2).2
  have hDone : D 1 = 1 := by
    simp only [hD, OneMemClass.coe_one, Units.val_one, Matrix.reindex_apply,
      Matrix.submatrix_one_equiv]
    exact toBlocks₂₂_one'
  have hDcomm : ∀ x y, D x * D y = D y * D x := fun x y => h.toBlocks₂₂_commute x.2 y.2
  have hDc : D (g * g' * g⁻¹ * g'⁻¹) = 1 := by
    rw [hDmul, hDmul, hDmul, mul_assoc (D g), hDcomm g', ← mul_assoc, ← hDmul, mul_inv_cancel,
      hDone, one_mul, ← hDmul, mul_inv_cancel, hDone]
  apply Units.ext
  apply (Matrix.reindex e e).injective
  rw [reindex_embHom, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h.coe_resGL,
    h.reindex_eq' (g * g' * g⁻¹ * g'⁻¹).2]
  exact congrArg _ hDc

theorem IsPairTorus.resGL_mem_orthGroup (h : IsPairTorus e δ ζ) {Q : (ι → K) → K}
    {Q' : (ι' → K) → K}
    (hQ : ∀ v : ι → K, Q v = Q' (fun x => v (e.symm (Sum.inl x))) +
      v (e.symm (Sum.inr (Sum.inl 0))) * v (e.symm (Sum.inr (Sum.inr 0))))
    (g : Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K)))
    (hgO : (g : GL ι K) ∈ LargeEvenOrthGroup Q) : h.resGL g ∈ LargeEvenOrthGroup Q' := by
  apply TableBSymp.mem_orthGroup_of_isometry
  intro w
  set v : ι → K := fun i => Sum.elim w 0 (e i) with hv
  have hve : v ∘ e.symm = Sum.elim w 0 := by
    funext z
    simp [hv]
  have hgv : ((g : GL ι K) : Matrix ι ι K) *ᵥ v =
      fun i => Sum.elim (((h.resGL g : GL ι' K) : Matrix ι' ι' K) *ᵥ w) 0 (e i) := by
    funext i
    obtain ⟨z, rfl⟩ := e.symm.surjective i
    rw [mulVec_reindex, h.reindex_eq' g.2, hve, Matrix.fromBlocks_mulVec, Equiv.apply_symm_apply,
      h.coe_resGL]
    rcases z with x | a <;> simp
  have h1 := isometry_of_mem_orthGroup hgO v
  rw [hgv, hQ, hQ] at h1
  simpa [hv] using h1

theorem IsPairTorus.embHom_mem_centralizer (h : IsPairTorus e δ ζ) (x : GL ι' K) :
    embHom e x ∈ Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  apply (Matrix.reindex e e).injective
  have hd : Matrix.reindex e e ((TauCeti.diagGL δ : GL ι K) : Matrix ι ι K) =
      Matrix.fromBlocks 1 0 0 (Matrix.diagonal fun a => ((δ (e.symm (Sum.inr a)) : Kˣ) : K)) := by
    rw [TauCeti.diagGL_coe]
    ext z w
    rcases z with x | a <;> rcases w with y | b <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, h.rest]
  rw [Units.val_mul, Units.val_mul, reindex_mul, reindex_mul, reindex_embHom, hd,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem IsPairTorus.commutator_mem_map_embHom_omega (h : IsPairTorus e δ ζ)
    {Q : (ι → K) → K} {Q' : (ι' → K) → K}
    (hQ : ∀ v : ι → K, Q v = Q' (fun x => v (e.symm (Sum.inl x))) +
      v (e.symm (Sum.inr (Sum.inl 0))) * v (e.symm (Sum.inr (Sum.inr 0))))
    {g g' : GL ι K} (hg : g ∈ Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K)))
    (hg' : g' ∈ Subgroup.centralizer ({TauCeti.diagGL δ} : Set (GL ι K)))
    (hgO : g ∈ LargeEvenOrthGroup Q) (hg'O : g' ∈ LargeEvenOrthGroup Q) :
    g * g' * g⁻¹ * g'⁻¹ ∈ (LargeEvenOmega Q').map (embHom e) := by
  have := h.commutator_eq ⟨g, hg⟩ ⟨g', hg'⟩
  refine ⟨_, ?_, this.symm⟩
  exact Subgroup.commutator_mem_commutator (h.resGL_mem_orthGroup hQ ⟨g, hg⟩ hgO)
    (h.resGL_mem_orthGroup hQ ⟨g', hg'⟩ hg'O)

end Centralizer

end TableBOrth

end CFSG.StandardType
