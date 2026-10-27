module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r ε : ℕ}

theorem inr_mem_semilinearSimilitudes (σ : K ≃+* K) :
    (SemidirectProduct.inr σ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε :=
  ⟨1, one_ne_zero, map_one _, by simp⟩

theorem glAut_mem_hypSU (σ : K ≃+* K) (g : hypSU h r ε) :
    glAut σ (g : GL (HypIndex r ε) K) ∈ hypSU h r ε := by
  have := conj_mem_hypSU (inr_mem_semilinearSimilitudes h σ) g
  simpa using this

@[expose] noncomputable def fieldHom (σ : K ≃+* K) : hypSU h r ε →* hypSU h r ε where
  toFun g := ⟨glAut σ (g : GL (HypIndex r ε) K), glAut_mem_hypSU h σ g⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem coe_fieldHom (σ : K ≃+* K) (g : hypSU h r ε) :
    ((fieldHom h σ g : hypSU h r ε) : GL (HypIndex r ε) K) = glAut σ (g : GL (HypIndex r ε) K) :=
  rfl

theorem mat_fieldHom (σ : K ≃+* K) (g : hypSU h r ε) :
    (((fieldHom h σ g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
    (((g : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K).map σ := rfl

theorem fieldHom_mul (σ τ : K ≃+* K) (g : hypSU h r ε) :
    fieldHom h (σ * τ) g = fieldHom h σ (fieldHom h τ g) :=
  Subtype.ext (by rw [coe_fieldHom, coe_fieldHom, coe_fieldHom, map_mul]; rfl)

theorem fieldHom_one (g : hypSU h r ε) : fieldHom h 1 g = g :=
  Subtype.ext (by rw [coe_fieldHom, map_one]; rfl)

@[expose] noncomputable def fieldAut (σ : K ≃+* K) : MulAut ↥(hypSU h r ε) where
  toFun := fieldHom h σ
  invFun := fieldHom h σ⁻¹
  left_inv g := by
    rw [← fieldHom_mul, inv_mul_cancel, fieldHom_one]
  right_inv g := by
    rw [← fieldHom_mul, mul_inv_cancel, fieldHom_one]
  map_mul' := (fieldHom h σ).map_mul

theorem fieldAut_apply (σ : K ≃+* K) (g : hypSU h r ε) : fieldAut h σ g = fieldHom h σ g := rfl

variable (r ε) in
@[expose] noncomputable def fieldAutHom : (K ≃+* K) →* MulAut ↥(hypSU h r ε) where
  toFun := fieldAut h
  map_one' := MulEquiv.ext fun g => fieldHom_one h g
  map_mul' σ τ := MulEquiv.ext fun g => fieldHom_mul h σ τ g

theorem fieldAutHom_apply (σ : K ≃+* K) (g : hypSU h r ε) :
    fieldAutHom h r ε σ g = fieldHom h σ g := rfl

theorem fieldAut_mem_unitriangular (σ : K ≃+* K) (g : hypSU h r ε) :
    fieldAut h σ g ∈ hypUnitriangular h r ε ↔ g ∈ hypUnitriangular h r ε := by
  rw [mem_hypUnitriangular, mem_hypUnitriangular, fieldAut_apply, mat_fieldHom]
  have hb : ∀ M : Matrix (HypIndex r ε) (HypIndex r ε) K,
      (M.map σ).BlockTriangular fullPos ↔ M.BlockTriangular fullPos := by
    intro M
    constructor
    · intro hM i j hij
      exact σ.injective (by simpa using hM hij)
    · intro hM i j hij
      simp [hM hij]
  rw [hb]
  refine and_congr_right fun _ => forall_congr' fun a => ?_
  simp only [map_apply]
  constructor
  · intro h1
    exact σ.injective (by simpa using h1)
  · intro h1
    simp [h1]

theorem fieldAut_mem_torus (σ : K ≃+* K) {g : hypSU h r ε} (hg : g ∈ hypTorus h r ε) :
    fieldAut h σ g ∈ hypTorus h r ε := by
  obtain ⟨a, d, hd, hp, hgm⟩ := hg
  refine ⟨fun i => Units.map (σ : K →* K) (a i), fun k => Units.map (σ : K →* K) (d k),
    fun k => ?_, ?_, ?_⟩
  · have := congrArg σ (hd k)
    simpa [UnitaryFieldData.norm, map_bar_comm h σ] using this
  · have := congrArg σ hp
    simpa [torusRatio, map_prod, map_bar_comm h σ] using this
  · rw [fieldAut_apply, mat_fieldHom, hgm, diagonal_map (map_zero σ)]
    congr 1
    funext x
    rcases x with i | k | i <;> simp [torusEntries, map_bar_comm h σ]

theorem fieldAutHom_comm [Finite K] (σ τ : K ≃+* K) :
    fieldAutHom h r ε σ * fieldAutHom h r ε τ = fieldAutHom h r ε τ * fieldAutHom h r ε σ := by
  rw [← map_mul, ← map_mul, ringAut_mul_comm K σ τ]

theorem exists_mem_hypTorus_entry (hε : ε ≤ 1) (c : Kˣ) :
    ∃ g ∈ hypTorus h 2 ε,
      ((g : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) (.inl 0) (.inl 0) =
        (c : K) := by
  have hbb : ∀ x : K, h.bar (h.bar x) = x := h.bar_bar
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · let a : Fin 2 → Kˣ := ![c, Units.map (h.bar : K →* K) c]
    have hp : torusRatio h a (isEmptyElim : Fin 0 → Kˣ) = 1 := by
      have e0 : ∏ k : Fin 0, (((isEmptyElim k : Kˣ)) : K) = 1 := Fin.prod_univ_zero _
      rw [torusRatio, e0, mul_one, Fin.prod_univ_two]
      have h0 : (c : K) ≠ 0 := c.ne_zero
      have h1 : h.bar (c : K) ≠ 0 := by simp [h0]
      simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one, Units.coe_map, MonoidHom.coe_ofClass]
      rw [hbb]
      field_simp
    obtain ⟨g, hg, hm⟩ := torusMat_mem_hypSU h a (d := isEmptyElim) (fun k => isEmptyElim k) hp
    exact ⟨g, hg, by rw [hm, diagonal_apply_eq]; rfl⟩
  · let a : Fin 2 → Kˣ := ![c, 1]
    let d : Fin 1 → Kˣ := fun _ => Units.map (h.bar : K →* K) c * c⁻¹
    have hd : ∀ k, h.norm (d k : K) = 1 := by
      intro k
      have h0 : (c : K) ≠ 0 := c.ne_zero
      simp only [d, UnitaryFieldData.norm, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀, hbb]
      have h1 : h.bar (c : K) ≠ 0 := by simp [h0]
      field_simp
    have hp : torusRatio h a d = 1 := by
      rw [torusRatio, Fin.prod_univ_two, Fin.prod_univ_one]
      have h0 : (c : K) ≠ 0 := c.ne_zero
      have h1 : h.bar (c : K) ≠ 0 := by simp [h0]
      simp only [a, d, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one, map_one,
        div_one, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, Units.val_inv_eq_inv_val]
      field_simp
    obtain ⟨g, hg, hm⟩ := torusMat_mem_hypSU h a hd hp
    exact ⟨g, hg, by rw [hm, diagonal_apply_eq]; rfl⟩

theorem eq_one_of_fixes_torus (hε : ε ≤ 1) (σ : K ≃+* K)
    (hfix : ∀ g ∈ hypTorus h 2 ε, fieldAut h σ g = g) : σ = 1 := by
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨g, hg, hm⟩ := exists_mem_hypTorus_entry h hε (Units.mk0 x hx)
    have := congrArg (fun y : hypSU h 2 ε =>
      ((y : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) (.inl 0) (.inl 0))
      (hfix g hg)
    simp only [fieldAut_apply, mat_fieldHom, map_apply, hm] at this
    simpa using this

end CFSG.Quasithin.H13.Sec53F.Unit
