module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IW
public import CFSG.RankThree.PartOne.KF.F1322OmegaSeven
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutFinal
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  CFSG.QuasithinUnique.Ch1 CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem fixed_iff_mem_range_soProj {A : GL (Fin 3) (ZMod p)}
    (hA : (A : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ = A) (x : projectiveSL 3 (ZMod p)) :
    (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p)) x = x ↔
      x ∈ (soProj ((A⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))).range := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := exists_mem_soForm_of_fixed A hx
    exact ⟨y, hy⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩
    change (LinearFlag.conjAut 3 (ZMod p) A) (LinearFlag.dualAut 3 (ZMod p)
      (proj 3 (ZMod p) y)) = proj 3 (ZMod p) y
    have hyR : (y : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ *
        ((A⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) * y =
          ((A⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := hy
    clear hy
    set R := ((A⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) with hR
    have hRt : Rᵀ = R := transpose_inv_of_transpose_eq' A hA
    have hAR : (A : Matrix (Fin 3) (Fin 3) (ZMod p)) * R = 1 := by
      rw [hR, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    set Y := (y : Matrix (Fin 3) (Fin 3) (ZMod p)) with hY
    set Yi := ((y⁻¹ : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) with hYi
    have hYYi : Y * Yi = 1 := by
      rw [hY, hYi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hRY : R * Y = Yiᵀ * R := by
      have h1 : Yᵀ * R = R * Yi := by
        calc Yᵀ * R = Yᵀ * R * (Y * Yi) := by rw [hYYi, Matrix.mul_one]
          _ = (Yᵀ * R * Y) * Yi := by simp only [Matrix.mul_assoc]
          _ = R * Yi := by rw [hyR]
      have h2 := congrArg Matrix.transpose h1
      rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hRt] at h2
    rw [LinearFlag.dualAut_proj, LinearFlag.conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [LinearFlag.coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
    calc (A : Matrix (Fin 3) (Fin 3) (ZMod p)) * Yiᵀ * R = A * (R * Y) := by
          rw [Matrix.mul_assoc, ← hRY]
      _ = Y := by rw [← Matrix.mul_assoc, hAR, Matrix.one_mul]

theorem map_toGL_soForm (R : Matrix (Fin 3) (Fin 3) (ZMod p)) :
    (soForm R).map Matrix.SpecialLinearGroup.toGL = soGL R := by
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨hs, s.2⟩
  · rintro ⟨hg, hdet⟩
    exact ⟨⟨g, hdet⟩, hg, Units.ext rfl⟩

theorem map_toGL_commutator_soForm (R : Matrix (Fin 3) (Fin 3) (ZMod p)) :
    (⁅soForm R, soForm R⁆ : Subgroup SL(3, ZMod p)).map Matrix.SpecialLinearGroup.toGL =
      omegaGL R := by
  rw [Subgroup.map_commutator, map_toGL_soForm]
  rfl

theorem commutator_soForm_le (R : Matrix (Fin 3) (Fin 3) (ZMod p)) :
    (⁅soForm R, soForm R⁆ : Subgroup SL(3, ZMod p)) ≤ soForm R := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact (soForm R).mul_mem ((soForm R).mul_mem ((soForm R).mul_mem ha hb) ((soForm R).inv_mem ha))
    ((soForm R).inv_mem hb)

theorem injective_proj_commutator_soForm {R : Matrix (Fin 3) (Fin 3) (ZMod p)} (hR : R ≠ 0) :
    Function.Injective ((proj 3 (ZMod p)).comp
      (⁅soForm R, soForm R⁆ : Subgroup SL(3, ZMod p)).subtype) := by
  intro a a' h
  have h1 : soProj R ⟨a, commutator_soForm_le R a.2⟩ =
      soProj R ⟨a', commutator_soForm_le R a'.2⟩ := h
  have h2 := congrArg Subtype.val (soProj_injective hR h1)
  exact Subtype.ext h2

theorem nonempty_commutator_soForm_equiv (hp : 5 ≤ p) {R : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (hRt : Rᵀ = R) (hRd : R.det ≠ 0) :
    Nonempty (↥(⁅soForm R, soForm R⁆ : Subgroup SL(3, ZMod p)) ≃* PSL(2, ZMod p)) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.KF1322.nonempty_omegaGL_equiv_psl2 hp hRt hRd
  exact ⟨((⁅soForm R, soForm R⁆ : Subgroup SL(3, ZMod p)).equivMapOfInjective _
    Matrix.SpecialLinearGroup.toGL_injective).trans
      ((MulEquiv.subgroupCongr (map_toGL_commutator_soForm R)).trans e)⟩

theorem two_ne_zero_and_sq_ne_one (hp : 5 ≤ p) : (2 : ZMod p) ≠ 0 ∧ (2 : ZMod p) ^ 2 ≠ 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd two_pos h1
    omega
  · have h1 : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega

theorem isPerfect_psl2_zmod (hp : 5 ≤ p) : Group.IsPerfect PSL(2, ZMod p) :=
  ⟨SL2Simple.PSL_commutator_eq_top ⟨2, two_ne_zero_and_sq_ne_one hp⟩⟩

theorem exists_ne_comm_psl2_zmod (hp : 5 ≤ p) : ∃ a b : PSL(2, ZMod p), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have := isPerfect_psl2_zmod hp
  exact Group.IsPerfect.not_isMulCommutative PSL(2, ZMod p) ⟨⟨h⟩⟩

theorem eq_one_of_commute_commutator_soForm (hp : 5 ≤ p) {R : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (hRt : Rᵀ = R) (hRd : R.det ≠ 0) {x : projectiveSL 3 (ZMod p)}
    (hx : ∀ ω ∈ (⁅soForm R, soForm R⁆ : Subgroup SL(3, ZMod p)),
      x * proj 3 (ZMod p) ω = proj 3 (ZMod p) ω * x) : x = 1 := by
  set W : Subgroup SL(3, ZMod p) := ⁅soForm R, soForm R⁆ with hW
  obtain ⟨X, rfl⟩ := proj_surjective 3 (ZMod p) x
  have hcen : ∀ ω ∈ W, X * ω * X⁻¹ * ω⁻¹ ∈ Subgroup.center SL(3, ZMod p) := by
    intro ω hω
    refine scalars_le_center 3 (ZMod p) (proj_eq_one_iff.mp ?_)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx ω hω]
    group
  let c : ↥W →* SL(3, ZMod p) := MonoidHom.mk' (fun ω => X * ω * X⁻¹ * (ω : SL(3, ZMod p))⁻¹)
    (fun ω₁ ω₂ => by
      have h2 := Subgroup.mem_center_iff.mp (hcen ω₂ ω₂.2)
      simp only [Subgroup.coe_mul]
      calc X * (↑ω₁ * ↑ω₂) * X⁻¹ * (↑ω₁ * ↑ω₂)⁻¹
          = (X * ↑ω₁ * X⁻¹) * (X * ↑ω₂ * X⁻¹ * (↑ω₂)⁻¹) * (↑ω₁)⁻¹ := by group
        _ = (X * ↑ω₂ * X⁻¹ * (↑ω₂)⁻¹) * (X * ↑ω₁ * X⁻¹) * (↑ω₁)⁻¹ := by
          rw [h2 (X * ↑ω₁ * X⁻¹)]
        _ = (X * ↑ω₂ * X⁻¹ * (↑ω₂)⁻¹) * (X * ↑ω₁ * X⁻¹ * (↑ω₁)⁻¹) := by group
        _ = (X * ↑ω₁ * X⁻¹ * (↑ω₁)⁻¹) * (X * ↑ω₂ * X⁻¹ * (↑ω₂)⁻¹) := (h2 _).symm)
  obtain ⟨eW⟩ := nonempty_commutator_soForm_equiv hp hRt hRd
  have := isPerfect_psl2_zmod hp
  have : Group.IsPerfect ↥W :=
    Group.IsPerfect.ofSurjective (f := eW.symm.toMonoidHom) eW.symm.surjective
  have hrc : ∀ a ∈ c.range, a ∈ Subgroup.center SL(3, ZMod p) := by
    rintro _ ⟨ω, rfl⟩
    exact hcen ω ω.2
  have : IsMulCommutative c.range :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp (hrc b b.2)) a)⟩⟩
  have : Group.IsPerfect c.range := Group.IsPerfect.range c
  have hc1 : ∀ ω : ↥W, X * ω = ω * X := by
    intro ω
    have h1 := congrArg Subtype.val (Subsingleton.elim (⟨c ω, ω, rfl⟩ : c.range) 1)
    have h2 : X * ω * X⁻¹ * (ω : SL(3, ZMod p))⁻¹ = 1 := h1
    calc X * ω = X * ω * X⁻¹ * (ω : SL(3, ZMod p))⁻¹ * (ω * X) := by group
      _ = ω * X := by rw [h2, one_mul]
  have hXc : ∀ g ∈ omegaGL R, Matrix.SpecialLinearGroup.toGL X * g =
      g * Matrix.SpecialLinearGroup.toGL X := by
    rw [← map_toGL_commutator_soForm R]
    rintro _ ⟨ω, hω, rfl⟩
    have h3 : X * ω = ω * X := hc1 ⟨ω, hω⟩
    rw [← map_mul, ← map_mul, h3]
  have hXs := eq_scalar_of_mem_centralizer_omegaGL hp hRt hRd hXc
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hXs
  set a := (X : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0
  have ha3 : a ^ 3 = 1 := by
    have h : (X : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := X.2
    rw [hXs, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  have ha0 : a ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by norm_num)] at ha3
    exact zero_ne_one ha3
  rw [proj_eq_one_iff, mem_scalars]
  refine ⟨Units.mk0 a ha0, Units.ext ?_, hXs⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, ha3, Units.val_one]

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
