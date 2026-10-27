module

public import CFSG.RankThree.PartOne.CTP.Spectrum

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F]

theorem glInv_mulVec (P : GL (Fin 3) F) (v : Fin 3 → F) :
    ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((P : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_mulVec_inv (P : GL (Fin 3) F) (v : Fin 3 → F) :
    (P : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_blkGroup_map_iff (P : GL (Fin 3) F) (W ℓ : Submodule F (Fin 3 → F))
    {g g' : SL(3, F)}
    (h : (g' : Matrix (Fin 3) (Fin 3) F) =
      (P : Matrix (Fin 3) (Fin 3) F) * g * ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    g' ∈ blkGroup F (W.map (Matrix.mulVecLin (P : Matrix (Fin 3) (Fin 3) F)))
        (ℓ.map (Matrix.mulVecLin (P : Matrix (Fin 3) (Fin 3) F))) ↔ g ∈ blkGroup F W ℓ := by
  have hP : ∀ u, (g' : Matrix (Fin 3) (Fin 3) F) *ᵥ ((P : Matrix (Fin 3) (Fin 3) F) *ᵥ u) =
      (P : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ u) := by
    intro u
    rw [h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, glInv_mulVec]
  have hinj : ∀ x y, (P : Matrix (Fin 3) (Fin 3) F) *ᵥ x = (P : Matrix (Fin 3) (Fin 3) F) *ᵥ y →
      x = y := by
    intro x y hxy
    have := congrArg (fun z => ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z) hxy
    simpa [glInv_mulVec] using this
  have hmemmap : ∀ (S : Submodule F (Fin 3 → F)) (u : Fin 3 → F),
      (P : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈
          S.map (Matrix.mulVecLin (P : Matrix (Fin 3) (Fin 3) F)) ↔ u ∈ S := by
    intro S u
    constructor
    · rintro ⟨x, hx, hxu⟩
      have : x = u := hinj _ _ (by simpa using hxu)
      exact this ▸ hx
    · intro hu
      exact ⟨u, hu, by simp⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun u hu => ?_, fun u => ?_⟩
    · have := h1 ((P : Matrix (Fin 3) (Fin 3) F) *ᵥ u) ⟨u, hu, by simp⟩
      rw [hP] at this
      exact hinj _ _ this
    · have := h2 ((P : Matrix (Fin 3) (Fin 3) F) *ᵥ u)
      rw [hP, hmemmap, hmemmap] at this
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · obtain ⟨u, hu, rfl⟩ := hv
      simp only [Matrix.mulVecLin_apply]
      rw [hP, h1 u hu]
    · obtain ⟨v', rfl⟩ : ∃ v', v = (P : Matrix (Fin 3) (Fin 3) F) *ᵥ v' :=
        ⟨((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v, (gl_mulVec_inv P v).symm⟩
      rw [hP, hmemmap, hmemmap]
      exact h2 v'

private theorem exists_adapted_basis {W ℓ : Submodule F (Fin 3 → F)} (hc : IsCompl W ℓ)
    (hW : Module.finrank F W = 2) :
    ∃ b : Module.Basis (Fin 3) F (Fin 3 → F),
      W = Submodule.span F {b 0, b 1} ∧ ℓ = Submodule.span F {b 2} := by
  have hℓ : Module.finrank F ℓ = 1 := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    rw [Module.finrank_fin_fun, hW] at this
    omega
  let bW : Module.Basis (Fin 2) F W := Module.finBasisOfFinrankEq F W hW
  let bℓ : Module.Basis (Fin 1) F ℓ := Module.finBasisOfFinrankEq F ℓ hℓ
  let e := Submodule.prodEquivOfIsCompl W ℓ hc
  let b' : Module.Basis (Fin 2 ⊕ Fin 1) F (Fin 3 → F) := (bW.prod bℓ).map e
  let b : Module.Basis (Fin 3) F (Fin 3 → F) := b'.reindex finSumFinEquiv
  have hb0 : b 0 = (bW 0 : Fin 3 → F) := by
    have : (finSumFinEquiv (m := 2) (n := 1)).symm (0 : Fin 3) = Sum.inl 0 := by decide
    simp only [b, b', Module.Basis.reindex_apply, this, Module.Basis.map_apply]
    simp [e, Submodule.coe_prodEquivOfIsCompl']
  have hb1 : b 1 = (bW 1 : Fin 3 → F) := by
    have : (finSumFinEquiv (m := 2) (n := 1)).symm (1 : Fin 3) = Sum.inl 1 := by decide
    simp only [b, b', Module.Basis.reindex_apply, this, Module.Basis.map_apply]
    simp [e, Submodule.coe_prodEquivOfIsCompl']
  have hb2 : b 2 = (bℓ 0 : Fin 3 → F) := by
    have : (finSumFinEquiv (m := 2) (n := 1)).symm (2 : Fin 3) = Sum.inr 0 := by decide
    simp only [b, b', Module.Basis.reindex_apply, this, Module.Basis.map_apply]
    simp [e, Submodule.coe_prodEquivOfIsCompl']
  refine ⟨b, ?_, ?_⟩
  · refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · exact Submodule.span_le.mpr (by
        rintro z (rfl | rfl)
        · exact hb0 ▸ (bW 0).2
        · exact hb1 ▸ (bW 1).2)
    · rw [finrank_span_pair_basis, hW]
  · refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · exact Submodule.span_le.mpr (by simpa using hb2 ▸ (bℓ 0).2)
    · rw [finrank_span_singleton (b.ne_zero 2), hℓ]

private theorem blkGroup_sub_mem {W ℓ : Submodule F (Fin 3 → F)} (hc : IsCompl W ℓ)
    {g : SL(3, F)} (hg : g ∈ blkGroup F W ℓ) (y : Fin 3 → F) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ y - y ∈ W := by
  obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top (x := y))
  rw [Matrix.mulVec_add, hg.1 u hu]
  have hgw : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W := (hg.2 w).mpr hw
  have : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w + u - (w + u) =
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w := by abel
  rw [this]
  exact W.sub_mem hgw hw

private theorem exists_sl_transvection (b : Module.Basis (Fin 3) F (Fin 3 → F)) {i j : Fin 3}
    (hij : i ≠ j) :
    ∃ g : SL(3, F), ∀ x, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x + (b.repr x j) • b i := by
  let f : (Fin 3 → F) →ₗ[F] (Fin 3 → F) := LinearMap.id + (b.coord j).smulRight (b i)
  have hf : ∀ x, f x = x + (b.repr x j) • b i := fun x => by simp [f]
  have hmat : LinearMap.toMatrix b b f = Matrix.transvection i j 1 := by
    ext k l
    rw [LinearMap.toMatrix_apply, hf]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      Module.Basis.repr_self, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul]
    by_cases h1 : l = k <;> by_cases h2 : l = j <;> by_cases h3 : i = k <;> simp_all [eq_comm]
  have hdet : (LinearMap.toMatrix' f).det = 1 := by
    rw [LinearMap.det_toMatrix', ← LinearMap.det_toMatrix b, hmat,
      Matrix.det_transvection_of_ne _ _ hij]
  refine ⟨⟨LinearMap.toMatrix' f, hdet⟩, fun x => ?_⟩
  show (LinearMap.toMatrix' f) *ᵥ x = _
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', hf]

private theorem transvection_mem_blkGroup (b : Module.Basis (Fin 3) F (Fin 3 → F)) {i j : Fin 3}
    (hi : i ≠ 2) (hj : j ≠ 2) {g : SL(3, F)}
    (hg : ∀ x, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x + (b.repr x j) • b i) :
    g ∈ blkGroup F (Submodule.span F {b 0, b 1}) (Submodule.span F {b 2}) := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [hg]
    have : b.repr (s • b 2) j = 0 := by
      simp [Module.Basis.repr_self, Ne.symm hj]
    rw [this, zero_smul, add_zero]
  · have h0 : b.repr (b i) 2 = 0 := by
      simp [Module.Basis.repr_self, Ne.symm hi]
    have h2 : ∀ x, b.repr ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = b.repr x 2 := by
      intro x
      rw [hg, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, h0, smul_zero, add_zero]
    rw [mem_span_pair_iff_repr, mem_span_pair_iff_repr, h2]

theorem normalizer_blkGroup {W ℓ : Submodule F (Fin 3 → F)} (hc : IsCompl W ℓ)
    (hW : Module.finrank F W = 2) (M : Matrix (Fin 3) (Fin 3) F) (hM : IsUnit M)
    (h1 : ∀ g ∈ blkGroup F W ℓ, ∃ g' ∈ blkGroup F W ℓ,
      M * (g : Matrix (Fin 3) (Fin 3) F) = (g' : Matrix (Fin 3) (Fin 3) F) * M)
    (h2 : ∀ h ∈ blkGroup F W ℓ, ∃ g ∈ blkGroup F W ℓ,
      (h : Matrix (Fin 3) (Fin 3) F) * M = M * (g : Matrix (Fin 3) (Fin 3) F)) :
    (∀ v ∈ ℓ, M *ᵥ v ∈ ℓ) ∧ (∀ v ∈ W, M *ᵥ v ∈ W) := by
  have _ := hM
  obtain ⟨b, rfl, rfl⟩ := exists_adapted_basis hc hW
  obtain ⟨t01, ht01⟩ := exists_sl_transvection b (i := 0) (j := 1) (by decide)
  obtain ⟨t10, ht10⟩ := exists_sl_transvection b (i := 1) (j := 0) (by decide)
  have hm01 := transvection_mem_blkGroup b (i := 0) (j := 1) (by decide) (by decide) ht01
  have hm10 := transvection_mem_blkGroup b (i := 1) (j := 0) (by decide) (by decide) ht10
  have hself : ∀ (i : Fin 3), b.repr (b i) i = 1 := fun i => by simp [Module.Basis.repr_self]
  have hline : ∀ v ∈ Submodule.span F {b 2}, M *ᵥ v ∈ Submodule.span F {b 2} := by
    intro v hv
    have hfix : ∀ t : SL(3, F), t ∈ blkGroup F (Submodule.span F {b 0, b 1})
        (Submodule.span F {b 2}) → (t : Matrix (Fin 3) (Fin 3) F) *ᵥ (M *ᵥ v) = M *ᵥ v := by
      intro t ht
      obtain ⟨g, hg, hgt⟩ := h2 t ht
      rw [Matrix.mulVec_mulVec, hgt, ← Matrix.mulVec_mulVec, hg.1 v hv]
    have e01 := hfix t01 hm01
    have e10 := hfix t10 hm10
    rw [ht01] at e01
    rw [ht10] at e10
    rw [mem_span_single_iff_repr]
    refine ⟨?_, ?_⟩
    · have : (b.repr (M *ᵥ v) 0) • b 1 = 0 := by
        have := congrArg (fun z => z - M *ᵥ v) e10
        simpa using this
      exact (smul_eq_zero.mp this).resolve_right (b.ne_zero 1)
    · have : (b.repr (M *ᵥ v) 1) • b 0 = 0 := by
        have := congrArg (fun z => z - M *ᵥ v) e01
        simpa using this
      exact (smul_eq_zero.mp this).resolve_right (b.ne_zero 0)
  refine ⟨hline, ?_⟩
  have hb0 : M *ᵥ b 0 ∈ Submodule.span F {b 0, b 1} := by
    obtain ⟨g', hg', hgg⟩ := h1 t01 hm01
    have e : M *ᵥ b 0 = (g' : Matrix (Fin 3) (Fin 3) F) *ᵥ (M *ᵥ b 1) - M *ᵥ b 1 := by
      have e1 : b 0 = (t01 : Matrix (Fin 3) (Fin 3) F) *ᵥ b 1 - b 1 := by
        rw [ht01, hself 1]; simp
      conv_lhs => rw [e1]
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hgg, ← Matrix.mulVec_mulVec]
    rw [e]
    exact blkGroup_sub_mem hc hg' (M *ᵥ b 1)
  have hb1 : M *ᵥ b 1 ∈ Submodule.span F {b 0, b 1} := by
    obtain ⟨g', hg', hgg⟩ := h1 t10 hm10
    have e : M *ᵥ b 1 = (g' : Matrix (Fin 3) (Fin 3) F) *ᵥ (M *ᵥ b 0) - M *ᵥ b 0 := by
      have e1 : b 1 = (t10 : Matrix (Fin 3) (Fin 3) F) *ᵥ b 0 - b 0 := by
        rw [ht10, hself 0]; simp
      conv_lhs => rw [e1]
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hgg, ← Matrix.mulVec_mulVec]
    rw [e]
    exact blkGroup_sub_mem hc hg' (M *ᵥ b 0)
  intro v hv
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hv
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hb0) (Submodule.smul_mem _ _ hb1)

end CFSG.RankThree.PartOne.CTP
