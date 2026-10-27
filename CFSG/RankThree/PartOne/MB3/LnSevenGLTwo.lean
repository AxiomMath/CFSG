module

public import CFSG.RankThree.PartOne.MB3.LnSevenEight
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import CFSG.RankThree.PartOne.MB3.LnSevenTwo

public section

namespace CFSG.RankThree.PartOne.MB3

open Matrix Polynomial Subgroup
open scoped commutatorElement

noncomputable section

variable {κ : Type} [Fintype κ] [DecidableEq κ]

@[expose] def Ψ (g : Matrix (Fin 2) (Fin 2) F8) :
    Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2) :=
  bd2 (phi (g 0 0)) (phi (g 0 1)) (phi (g 1 0)) (phi (g 1 1))

theorem Ψ_mul (g h : Matrix (Fin 2) (Fin 2) F8) :
    (Ψ (g * h) : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) = Ψ g * Ψ h := by
  simp only [Ψ, bd2_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]

omit [Fintype κ] in
theorem Ψ_one : (Ψ (1 : Matrix (Fin 2) (Fin 2) F8) :
    Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) = 1 := by
  simp [Ψ, bd2]

omit [Fintype κ] in
theorem Ψ_injective : Function.Injective
    (Ψ : Matrix (Fin 2) (Fin 2) F8 →
      Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
  intro g h hgh
  obtain ⟨h00, h01, h10, h11⟩ := bd2_inj hgh
  ext a b
  fin_cases a <;> fin_cases b
  · exact phi_injective h00
  · exact phi_injective h01
  · exact phi_injective h10
  · exact phi_injective h11

theorem Ψ_det (g : Matrix.GeneralLinearGroup (Fin 2) F8) :
    (Ψ (g : Matrix (Fin 2) (Fin 2) F8) :
      Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)).det = 1 := by
  have h1 : (Ψ (g : Matrix (Fin 2) (Fin 2) F8) :
      Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) *
        Ψ ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F8) : Matrix (Fin 2) (Fin 2) F8) = 1 := by
    rw [← Ψ_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Ψ_one]
  have h2 := Matrix.isUnit_det_of_right_inverse h1
  have key : ∀ x : ZMod 2, IsUnit x → x = 1 := by
    intro x hx
    fin_cases x
    · exact absurd hx not_isUnit_zero
    · rfl
  exact key _ h2

@[expose] def Γ : Matrix.GeneralLinearGroup (Fin 2) F8 →*
    SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2) where
  toFun g := ⟨Ψ (g : Matrix (Fin 2) (Fin 2) F8), Ψ_det g⟩
  map_one' := Subtype.ext (by
    show Ψ ((1 : Matrix.GeneralLinearGroup (Fin 2) F8) : Matrix (Fin 2) (Fin 2) F8) = 1
    rw [Units.val_one, Ψ_one])
  map_mul' g h := by
    refine Subtype.ext ?_
    show Ψ (↑(g * h) : Matrix (Fin 2) (Fin 2) F8) = Ψ ↑g * Ψ ↑h
    rw [Units.val_mul, Ψ_mul]

theorem coe_Γ (g : Matrix.GeneralLinearGroup (Fin 2) F8) :
    ((Γ g : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) :
      Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) =
        Ψ (g : Matrix (Fin 2) (Fin 2) F8) := rfl

theorem Γ_injective : Function.Injective
    (Γ : Matrix.GeneralLinearGroup (Fin 2) F8 →*
      SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
  intro g h hgh
  apply Units.ext
  exact Ψ_injective (congrArg Subtype.val hgh)

variable (κ) in
@[expose] def β₂ : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2) :=
  ⟨bd2 cM 0 0 cM, by
    rw [bd2_det, det_fromBlocks_zero₂₁, cM_det]
    simp⟩

theorem coe_β₂ : ((β₂ κ : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) :
    Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) = bd2 cM 0 0 cM := rfl

@[expose] def T₂ : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) :=
  Subgroup.centralizer {(β₂ κ : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))}

theorem mem_T₂ {A : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)} :
    A ∈ (T₂ : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))) ↔
      A * β₂ κ = β₂ κ * A := by
  rw [T₂, Subgroup.mem_centralizer_singleton_iff]

theorem Γ_mem_T₂ (g : Matrix.GeneralLinearGroup (Fin 2) F8) :
    (Γ g : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) ∈ T₂ := by
  rw [mem_T₂]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_β₂, coe_Γ]
  simp only [Ψ, bd2_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [phi_comm, phi_comm, phi_comm, phi_comm]

theorem exists_Ψ_of_mem_T₂ (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1)
    {A : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)} (hA : A ∈ T₂) :
    ∃ g₀ : Matrix (Fin 2) (Fin 2) F8, (Ψ g₀ : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ)
      ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) = A := by
  have hA' := congrArg Subtype.val (mem_T₂.mp hA)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_β₂] at hA'
  obtain ⟨P, Q, R, S, hPQRS, hP, hQ, hR, hS, -⟩ :=
    exists_bd2_of_commute exists_inv_cM_sub_one hκ A.2 hA'
  obtain ⟨x₀₀, h00⟩ := exists_phi_eq hP
  obtain ⟨x₀₁, h01⟩ := exists_phi_eq hQ.symm.symm
  obtain ⟨x₁₀, h10⟩ := exists_phi_eq hR.symm.symm
  obtain ⟨x₁₁, h11⟩ := exists_phi_eq hS
  refine ⟨!![x₀₀, x₀₁; x₁₀, x₁₁], ?_⟩
  rw [hPQRS]
  simp [Ψ, h00, h01, h10, h11]

theorem exists_Γ_of_mem_T₂ (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1)
    {A : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)} (hA : A ∈ T₂) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) F8, Γ g = A := by
  obtain ⟨g₀, hg₀⟩ := exists_Ψ_of_mem_T₂ hκ hA
  obtain ⟨g₁, hg₁⟩ := exists_Ψ_of_mem_T₂ hκ (inv_mem hA)
  have h1 : g₀ * g₁ = 1 := by
    apply Ψ_injective (κ := κ)
    rw [Ψ_mul, hg₀, hg₁, Ψ_one, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have h2 : g₁ * g₀ = 1 := by
    apply Ψ_injective (κ := κ)
    rw [Ψ_mul, hg₀, hg₁, Ψ_one, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  exact ⟨⟨g₀, g₁, h1, h2⟩, Subtype.ext (by rw [coe_Γ]; exact hg₀)⟩

@[expose] def Γ' : SpecialLinearGroup (Fin 2) F8 →*
    SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2) :=
  Γ.comp Matrix.SpecialLinearGroup.toGL

theorem Γ'_injective : Function.Injective
    (Γ' : SpecialLinearGroup (Fin 2) F8 →*
      SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) :=
  Γ_injective.comp Matrix.SpecialLinearGroup.toGL_injective

theorem Γ'_mem_T₂ (s : SpecialLinearGroup (Fin 2) F8) :
    (Γ' s : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) ∈ T₂ :=
  Γ_mem_T₂ _

theorem commutator_mem_range_Γ' (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1)
    (x y : ↥(T₂ : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)))) :
    ((⁅x, y⁆ : ↥(T₂ : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)))) :
      SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) ∈ (Γ' (κ := κ)).range := by
  obtain ⟨gx, hgx⟩ := exists_Γ_of_mem_T₂ hκ x.2
  obtain ⟨gy, hgy⟩ := exists_Γ_of_mem_T₂ hκ y.2
  have hdet : ⁅gx, gy⁆ ∈ (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin 2) F8 →* F8ˣ).ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    simp [commutatorElement_def]
  rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hdet
  obtain ⟨s, hs⟩ := hdet
  refine ⟨s, ?_⟩
  show Γ (Matrix.SpecialLinearGroup.toGL s) =
    ⁅(x : Matrix.SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)),
      (y : Matrix.SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))⁆
  rw [hs, map_commutatorElement, hgx, hgy]

theorem center_sl2_F8 : Subgroup.center (SpecialLinearGroup (Fin 2) F8) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F8) = 0 := CharTwo.two_eq_zero
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  subst hr1
  rw [Subgroup.mem_bot]
  ext i j
  have := congrFun (congrFun hrA i) j
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

@[expose] def slPslEquiv_F8 :
    SpecialLinearGroup (Fin 2) F8 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F8 :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq center_sl2_F8.symm)

theorem isSimpleGroup_sl2_F8 : IsSimpleGroup (SpecialLinearGroup (Fin 2) F8) := by
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F8) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [card_F8]; norm_num)
  exact slPslEquiv_F8.isSimpleGroup

theorem eq_range_Γ'_of_isComponent (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1)
    {E : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))} (hE : E ≤ T₂)
    (hcomp : CFSG.IsComponent (E.subgroupOf T₂)) : E = (Γ' (κ := κ)).range := by
  have hS : (Γ' (κ := κ)).range ≤ T₂ := by
    rintro _ ⟨s, rfl⟩
    exact Γ'_mem_T₂ s
  have hsl : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F8) := isSimpleGroup_sl2_F8
  have hS' : IsSimpleGroup ↥((Γ' (κ := κ)).range.subgroupOf T₂) :=
    ((Subgroup.subgroupOfEquivOfLe hS).trans
      (MonoidHom.ofInjective Γ'_injective).symm).isSimpleGroup
  have h1 : E.subgroupOf T₂ = (Γ' (κ := κ)).range.subgroupOf T₂ := by
    refine eq_of_isComponent hS' (fun x y => ?_) hcomp
    exact commutator_mem_range_Γ' hκ x y
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hE, inf_eq_left.mpr hS] at h1
  exact h1

theorem nonempty_mulEquiv_of_isComponent_T₂
    (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1)
    {E : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))} (hE : E ≤ T₂)
    (hcomp : CFSG.IsComponent (E.subgroupOf T₂)) :
    Nonempty (↥E ≃* SpecialLinearGroup (Fin 2) F8) := by
  have h := eq_range_Γ'_of_isComponent hκ hE hcomp
  subst h
  exact ⟨(MonoidHom.ofInjective Γ'_injective).symm⟩

end

end CFSG.RankThree.PartOne.MB3
