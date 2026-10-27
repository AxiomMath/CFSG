module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAut
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitAut
public import CFSG.RankThree.PartOne.U5K.Hyp.Para

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open CFSG.QuasithinUnique
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.BA

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

@[expose] def inrGam (σ : K ≃+* K) : Gam hK :=
  ⟨SemidirectProduct.inr σ, inr_mem_semilinearSimilitudes hK σ⟩

@[expose] noncomputable def fieldP : (K ≃+* K) →* MulAut (hypPSU hK 2 1) where
  toFun σ := Phi hK (inrGam hK σ)
  map_one' := by
    rw [show inrGam hK 1 = 1 from Subtype.ext (map_one _), map_one]
  map_mul' σ τ := by
    rw [← map_mul]
    exact congrArg (Phi hK) (Subtype.ext (map_mul SemidirectProduct.inr σ τ))

theorem fieldP_apply (σ : K ≃+* K) (g : hypSU hK 2 1) :
    fieldP hK σ (hypProj hK 2 1 g) = hypProj hK 2 1 (fieldAut hK σ g) := by
  change Phi hK (inrGam hK σ) (hypProj hK 2 1 g) = _
  rw [Phi_apply]
  congr 1
  refine Subtype.ext ?_
  change (inrGam hK σ).1.left * glAut (inrGam hK σ).1.right (g : GL (HypIndex 2 1) K) *
    (inrGam hK σ).1.left⁻¹ = glAut σ (g : GL (HypIndex 2 1) K)
  simp [inrGam]

theorem map_fieldP_eq (σ : K ≃+* K) (X : Subgroup (hypSU hK 2 1))
    (hX : ∀ g, fieldAut hK σ g ∈ X ↔ g ∈ X) :
    (X.map (hypProj hK 2 1)).map (fieldP hK σ).toMonoidHom = X.map (hypProj hK 2 1) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨fieldAut hK σ x, (hX x).2 hx, (fieldP_apply hK σ x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' : (fieldAut hK σ)⁻¹ x ∈ X := by
      rw [← hX, MulAut.apply_inv_self]
      exact hx
    exact ⟨_, ⟨(fieldAut hK σ)⁻¹ x, hx', rfl⟩, by
      change fieldP hK σ _ = _
      rw [fieldP_apply, MulAut.apply_inv_self]⟩

theorem fieldP_stab (σ : K ≃+* K) (X : Subgroup (hypSU hK 2 1))
    (hX : ∀ g, fieldAut hK σ g ∈ X ↔ g ∈ X) (x : hypPSU hK 2 1) :
    fieldP hK σ x ∈ X.map (hypProj hK 2 1) ↔ x ∈ X.map (hypProj hK 2 1) := by
  have := Subgroup.mem_map_iff_mem (f := (fieldP hK σ).toMonoidHom) (fieldP hK σ).injective
    (K := X.map (hypProj hK 2 1)) (x := x)
  rwa [map_fieldP_eq hK σ X hX] at this

theorem fieldP_stab_U (σ : K ≃+* K) (x : hypPSU hK 2 1) :
    fieldP hK σ x ∈ hypProjUnitriangular hK 2 1 ↔ x ∈ hypProjUnitriangular hK 2 1 :=
  fieldP_stab hK σ _ (fieldAut_mem_unitriangular hK σ) x

theorem fieldP_stab_H (σ : K ≃+* K) (x : hypPSU hK 2 1) :
    fieldP hK σ x ∈ (hypTorus hK 2 1).map (hypProj hK 2 1) ↔
      x ∈ (hypTorus hK 2 1).map (hypProj hK 2 1) := by
  refine fieldP_stab hK σ _ (fun g => ⟨fun hg => ?_, fun hg => fieldAut_mem_torus hK σ hg⟩) x
  have := fieldAut_mem_torus hK σ⁻¹ hg
  have e : fieldAut hK σ⁻¹ (fieldAut hK σ g) = g := by
    rw [fieldAut_apply, fieldAut_apply, ← fieldHom_mul, inv_mul_cancel, fieldHom_one]
  rwa [e] at this

theorem fieldP_comm [Finite K] (σ τ : K ≃+* K) :
    fieldP hK σ * fieldP hK τ = fieldP hK τ * fieldP hK σ := by
  rw [← map_mul, ← map_mul, ringAut_mul_comm K σ τ]

theorem exists_mem_hypTorus_entry_five (c : Kˣ) :
    ∃ g ∈ hypTorus hK 2 1,
      ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (.inl 0) (.inl 0) =
        (c : K) ∧
      ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (.inl 1) (.inl 1) =
        1 := by
  have hbb : ∀ x : K, hK.bar (hK.bar x) = x := hK.bar_bar
  let a : Fin 2 → Kˣ := ![c, 1]
  let d : Fin 1 → Kˣ := fun _ => Units.map (hK.bar : K →* K) c * c⁻¹
  have h0 : (c : K) ≠ 0 := c.ne_zero
  have h1 : hK.bar (c : K) ≠ 0 := by simp [h0]
  have hd : ∀ k, hK.norm (d k : K) = 1 := by
    intro k
    simp only [d, UnitaryFieldData.norm, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass,
      Units.val_inv_eq_inv_val, map_mul, map_inv₀, hbb]
    field_simp
  have hp : torusRatio hK a d = 1 := by
    rw [torusRatio, Fin.prod_univ_two, Fin.prod_univ_one]
    simp only [a, d, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one, map_one,
      div_one, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, Units.val_inv_eq_inv_val]
    field_simp
  obtain ⟨g, hg, hm⟩ := torusMat_mem_hypSU hK a hd hp
  exact ⟨g, hg, by rw [hm, diagonal_apply_eq]; rfl, by rw [hm, diagonal_apply_eq]; rfl⟩

theorem eq_one_of_fieldP_fixes (σ : K ≃+* K)
    (hfix : ∀ x ∈ (hypTorus hK 2 1).map (hypProj hK 2 1), fieldP hK σ x = x) : σ = 1 := by
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨g, hg, hm0, hm1⟩ := exists_mem_hypTorus_entry_five hK (Units.mk0 x hx)
    have h1 := hfix _ ⟨g, hg, rfl⟩
    rw [fieldP_apply] at h1
    have hz : (fieldAut hK σ g)⁻¹ * g ∈ hypScalars hK 2 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    obtain ⟨μ, -, -, hμ⟩ := hz
    have h2 : (g : GL (HypIndex 2 1) K) = (fieldAut hK σ g : GL (HypIndex 2 1) K) *
        GeneralLinearGroup.scalar (HypIndex 2 1) μ := by
      have : (g : GL (HypIndex 2 1) K) = (fieldAut hK σ g : GL (HypIndex 2 1) K) *
          (((fieldAut hK σ g)⁻¹ * g : hypSU hK 2 1) : GL (HypIndex 2 1) K) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this, hμ]
    have hmat : ∀ i j, ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) i j =
        σ (((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) i j) * μ := by
      intro i j
      have := congrArg (fun M : GL (HypIndex 2 1) K =>
        (M : Matrix (HypIndex 2 1) (HypIndex 2 1) K) i j) h2
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.mul_diagonal] at this
      exact this
    have e1 := hmat (.inl 1) (.inl 1)
    have e0 := hmat (.inl 0) (.inl 0)
    rw [hm1, map_one, one_mul] at e1
    rw [hm0, ← e1, mul_one] at e0
    show σ x = x
    simpa using e0.symm

end CFSG.Quasithin.H13.Sec53F.Unit
