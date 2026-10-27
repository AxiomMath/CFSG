module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructure
public import CFSG.LocalAnalysis.StandardType.GGHypSixTypeA
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace AutPSL

section Graph

variable {n : ℕ} {K : Type*} [Field K] [CharP K 2]

noncomputable abbrev revSL : SpecialLinearGroup (Fin n) K :=
  ggPermSL (F := K) (Fin.revPerm : Equiv.Perm (Fin n))

@[expose] noncomputable def gammaSL : MulAut (SpecialLinearGroup (Fin n) K) :=
  MulAut.conj (revSL (n := n) (K := K)) *
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n K

@[expose] noncomputable def graphAut : MulAut (projectiveSL n K) :=
  conjAut n K (SpecialLinearGroup.toGL (revSL (n := n) (K := K))) * dualAut n K

theorem gammaSL_apply (g : SpecialLinearGroup (Fin n) K) :
    gammaSL g = revSL * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n K g *
      revSL⁻¹ :=
  rfl

theorem coe_gammaSL (g : SpecialLinearGroup (Fin n) K) :
    ((gammaSL g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).submatrix
        Fin.revPerm Fin.revPerm := by
  rw [gammaSL_apply, coe_ggPermSL_conj]
  rfl

omit [CharP K 2] in
theorem slConjugation_toGL (s g : SpecialLinearGroup (Fin n) K) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K
      (SpecialLinearGroup.toGL s) g = s * g * s⁻¹ := by
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  simp only [map_mul, map_inv]

omit [CharP K 2] in
theorem conjAut_toGL (s : SpecialLinearGroup (Fin n) K) :
    conjAut n K (SpecialLinearGroup.toGL s) = MulAut.conj (proj n K s) := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [conjAut_proj, slConjugation_toGL, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem graphAut_proj (g : SpecialLinearGroup (Fin n) K) :
    graphAut (proj n K g) = proj n K (gammaSL g) := by
  rw [graphAut, MulAut.mul_apply, dualAut_proj, conjAut_proj, slConjugation_toGL]
  rfl

theorem gammaSL_map (σ : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    gammaSL (SpecialLinearGroup.map σ.toRingHom g) =
      SpecialLinearGroup.map σ.toRingHom (gammaSL g) := by
  ext i j
  rw [coe_gammaSL, SpecialLinearGroup.map_apply_coe, coe_gammaSL, ← map_inv,
    SpecialLinearGroup.map_apply_coe]
  simp [Matrix.submatrix_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply]

theorem gammaSL_gammaSL (g : SpecialLinearGroup (Fin n) K) : gammaSL (gammaSL g) = g := by
  ext i j
  rw [coe_gammaSL, ← map_inv, coe_gammaSL, inv_inv]
  simp [Matrix.submatrix_apply]

theorem gammaSL_transvection {i j : Fin n} (hij : i ≠ j) (t : K) :
    gammaSL (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection (Fin.rev_injective.ne hij.symm) t := by
  ext a b
  rw [coe_gammaSL, SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, CharTwo.neg_eq]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single,
    Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Fin.revPerm_apply, Fin.rev_inj]
  congr 1
  have e1 : (j = Fin.rev a) ↔ (Fin.rev j = a) :=
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
  have e2 : (i = Fin.rev b) ↔ (Fin.rev i = b) :=
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
  simp only [e1, e2]

theorem graphAut_proj_transvection {i j : Fin n} (hij : i ≠ j) (t : K) :
    graphAut (proj n K (SpecialLinearGroup.transvection hij t)) =
      proj n K (SpecialLinearGroup.transvection (Fin.rev_injective.ne hij.symm) t) := by
  rw [graphAut_proj, gammaSL_transvection]

omit [CharP K 2] in
theorem fieldAut_proj_transvection (σ : K ≃+* K) {i j : Fin n} (hij : i ≠ j) (t : K) :
    fieldAut n K σ (proj n K (SpecialLinearGroup.transvection hij t)) =
      proj n K (SpecialLinearGroup.transvection hij (σ t)) := by
  rw [fieldAut_proj, SpecialLinearGroup.map_transvection]
  rfl

theorem graphAut_mul_self : (graphAut : MulAut (projectiveSL n K)) * graphAut = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [MulAut.mul_apply, graphAut_proj, graphAut_proj, gammaSL_gammaSL, MulAut.one_apply]

theorem graphAut_inv : (graphAut : MulAut (projectiveSL n K))⁻¹ = graphAut :=
  (eq_inv_of_mul_eq_one_left graphAut_mul_self).symm

theorem fieldAut_mul_graphAut (σ : K ≃+* K) :
    fieldAut n K σ * graphAut = graphAut * fieldAut n K σ := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [MulAut.mul_apply, MulAut.mul_apply, graphAut_proj, fieldAut_proj, fieldAut_proj,
    graphAut_proj, gammaSL_map]

end Graph

section Structure

variable {n : ℕ} {K : Type*} [Field K]

noncomputable abbrev inndiag : Subgroup (MulAut (projectiveSL n K)) :=
  (conjAut n K).range

theorem inn_le_inndiag :
    (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ inndiag := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  exact ⟨SpecialLinearGroup.toGL g, conjAut_toGL g⟩

theorem dualAut_conj_mem (A : GL (Fin n) K) :
    dualAut n K * conjAut n K A * (dualAut n K)⁻¹ ∈
      (inndiag : Subgroup (MulAut (projectiveSL n K))) := by
  have htr := standard_automorphism_transport (K := K) (n := n)
  have hδinv : (dualAut n K)⁻¹ = dualAut n K := (eq_inv_of_mul_eq_one_left htr.2.2.2.1).symm
  rw [hδinv, htr.2.2.2.2.1 A]
  exact ⟨_, rfl⟩

theorem fieldAut_conj_mem (σ : K ≃+* K) (A : GL (Fin n) K) :
    fieldAut n K σ * conjAut n K A * (fieldAut n K σ)⁻¹ ∈
      (inndiag : Subgroup (MulAut (projectiveSL n K))) := by
  rw [(standard_automorphism_transport (K := K) (n := n)).2.2.1 σ A]
  exact ⟨_, rfl⟩

theorem inndiag_normal [Finite K] (hn : 3 ≤ n) :
    (inndiag : Subgroup (MulAut (projectiveSL n K))).Normal := by
  show ((conjAut n K).range).Normal
  rw [← linearAutGroup_eq_range]
  exact linearAutGroup_normal_of_three_le hn

theorem odd_card_units [Finite K] [CharP K 2] : Odd (Nat.card Kˣ) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  rw [Nat.card_units, Nat.card_eq_fintype_card, hk]
  obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by have := k.pos; omega⟩
  rw [hj, pow_succ]
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  exact ⟨2 ^ j - 1, by omega⟩

theorem odd_relIndex_inn_inndiag [Finite K] [CharP K 2] :
    Odd ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range.relIndex
      (inndiag : Subgroup (MulAut (projectiveSL n K)))) := by
  set f := (conjAut n K).rangeRestrict
  have hInn : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range.subgroupOf
      (inndiag : Subgroup (MulAut (projectiveSL n K))) =
      (SpecialLinearGroup.toGL.range : Subgroup (GL (Fin n) K)).map f := by
    ext ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨g, rfl⟩ := proj_surjective n K y
      refine ⟨SpecialLinearGroup.toGL g, ⟨g, rfl⟩, Subtype.ext ?_⟩
      change conjAut n K (SpecialLinearGroup.toGL g) = x
      rw [conjAut_toGL]
      exact hy
    · rintro ⟨A, ⟨g, rfl⟩, hA⟩
      have hA' : conjAut n K (SpecialLinearGroup.toGL g) = x := congrArg Subtype.val hA
      refine ⟨proj n K g, ?_⟩
      change MulAut.conj (proj n K g) = x
      rw [← hA', conjAut_toGL]
  rw [Subgroup.relIndex, hInn]
  refine Odd.of_dvd_nat ?_ (Subgroup.index_map_dvd _ (MonoidHom.rangeRestrict_surjective _))
  rw [SpecialLinearGroup.range_toGL_eq_ker_det, Subgroup.index_ker]
  exact Odd.of_dvd_nat odd_card_units (Subgroup.card_subgroup_dvd_card _)

variable [CharP K 2]

@[expose] noncomputable def compl : Subgroup (MulAut (projectiveSL n K)) where
  carrier := {c | ∃ σ : K ≃+* K, c = fieldAut n K σ ∨ c = fieldAut n K σ * graphAut}
  mul_mem' := by
    rintro _ _ ⟨σ, rfl | rfl⟩ ⟨τ, rfl | rfl⟩
    · exact ⟨σ * τ, Or.inl (map_mul _ σ τ).symm⟩
    · exact ⟨σ * τ, Or.inr (by rw [map_mul, mul_assoc])⟩
    · refine ⟨σ * τ, Or.inr ?_⟩
      rw [map_mul, mul_assoc, ← fieldAut_mul_graphAut, mul_assoc]
    · refine ⟨σ * τ, Or.inl ?_⟩
      rw [map_mul, show fieldAut n K σ * graphAut * (fieldAut n K τ * graphAut) =
        fieldAut n K σ * (graphAut * fieldAut n K τ) * graphAut by group,
        ← fieldAut_mul_graphAut, mul_assoc, mul_assoc, graphAut_mul_self, mul_one]
  one_mem' := ⟨1, Or.inl (map_one _).symm⟩
  inv_mem' := by
    rintro _ ⟨σ, rfl | rfl⟩
    · exact ⟨σ⁻¹, Or.inl (map_inv _ σ).symm⟩
    · refine ⟨σ⁻¹, Or.inr ?_⟩
      rw [_root_.mul_inv_rev, graphAut_inv, ← map_inv]
      exact (fieldAut_mul_graphAut σ⁻¹).symm

theorem mem_compl {c : MulAut (projectiveSL n K)} :
    c ∈ (compl : Subgroup (MulAut (projectiveSL n K))) ↔
      ∃ σ : K ≃+* K, c = fieldAut n K σ ∨ c = fieldAut n K σ * graphAut :=
  Iff.rfl

theorem exists_mul_compl [Finite K] (hn : 3 ≤ n) (α : MulAut (projectiveSL n K)) :
    ∃ i ∈ (inndiag : Subgroup (MulAut (projectiveSL n K))), ∃ c ∈ compl, α = i * c := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) hn).2 α
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · exact ⟨conjAut n K A, ⟨A, rfl⟩, fieldAut n K σ, ⟨σ, Or.inl rfl⟩, by rw [pow_zero, mul_one]⟩
  ·
    set J := SpecialLinearGroup.toGL (revSL (n := n) (K := K))
    have hδ : dualAut n K = conjAut n K J⁻¹ * graphAut := by
      rw [graphAut, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    obtain ⟨A₂, hA₂⟩ := fieldAut_conj_mem σ J⁻¹
    refine ⟨conjAut n K A * conjAut n K A₂, mul_mem ⟨A, rfl⟩ ⟨A₂, rfl⟩,
      fieldAut n K σ * graphAut, ⟨σ, Or.inr rfl⟩, ?_⟩
    rw [pow_one, hδ, hA₂]
    group

theorem eq_one_of_fieldAut_mem (hn : 2 ≤ n) {σ : K ≃+* K}
    (h : fieldAut n K σ ∈ (inndiag : Subgroup (MulAut (projectiveSL n K)))) : σ = 1 := by
  obtain ⟨A, hA⟩ := h
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h1 : conjAut n K A⁻¹ * fieldAut n K σ = 1 := by
    rw [← hA, ← map_mul, inv_mul_cancel, map_one]
  refine HypSixTypeA.field_eq_one hij (A := A⁻¹) (V := 1) (W := 1) fun t => ?_
  have h2 := congrArg (fun α : MulAut (projectiveSL n K) =>
    α (proj n K (SpecialLinearGroup.transvection hij t))) h1
  simp only [MulAut.mul_apply, MulAut.one_apply, fieldAut_proj, conjAut_proj] at h2
  simpa using h2.symm

theorem inndiag_inf_compl [Finite K] (hn : 3 ≤ n) :
    (inndiag : Subgroup (MulAut (projectiveSL n K))) ⊓ compl = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨hcI, σ, rfl | rfl⟩
  · rw [eq_one_of_fieldAut_mem (by omega) hcI, map_one]
    exact Subgroup.one_mem _
  · exfalso
    obtain ⟨A, hA⟩ := hcI
    apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) hn
    have hδ : dualAut n K = (conjAut n K (SpecialLinearGroup.toGL (revSL (n := n) (K := K))))⁻¹ *
        (fieldAut n K σ)⁻¹ * conjAut n K A := by
      rw [hA, graphAut]
      group
    have hc : ∀ B : GL (Fin n) K, conjAut n K B ∈ semilinearAutGroup n K := fun B =>
      linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup B)
    rw [hδ]
    exact mul_mem (mul_mem (inv_mem (hc _)) (inv_mem (fieldAut_mem_semilinearAutGroup σ))) (hc _)

theorem involution_compl (hn : 2 ≤ n) {c : MulAut (projectiveSL n K)} (hc : c ∈ compl)
    (hc2 : c ^ 2 = 1) :
    ∃ σ : K ≃+* K, σ * σ = 1 ∧ (c = fieldAut n K σ ∨ c = fieldAut n K σ * graphAut) := by
  obtain ⟨σ, hσ⟩ := hc
  refine ⟨σ, eq_one_of_fieldAut_mem hn ?_, hσ⟩
  have hsq : fieldAut n K (σ * σ) = 1 := by
    rcases hσ with rfl | rfl
    · rw [map_mul, ← pow_two, hc2]
    · rw [map_mul, ← hc2, pow_two, show fieldAut n K σ * graphAut * (fieldAut n K σ * graphAut) =
        fieldAut n K σ * (graphAut * fieldAut n K σ) * graphAut by group,
        ← fieldAut_mul_graphAut, mul_assoc, mul_assoc, graphAut_mul_self, mul_one]
  rw [hsq]
  exact Subgroup.one_mem _

end Structure

end AutPSL

end CFSG.StandardType
