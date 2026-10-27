module

public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.RankThree.PartTwo.Sec4.StepsGraphField
import CFSG.RankThree.Asc83Table.E27
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (diagGL det_diagGL coe_diagGL)
open scoped commutatorElement

variable {k : Type*} [Field k]

theorem commutator_mul_self_eq_one {G : Type*} [Group G] {g x y c₁ c₂ : G}
    (hz : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center G) (hc₁ : c₁ ∈ Subgroup.center G)
    (hc₂ : c₂ ∈ Subgroup.center G) (h₁ : g * x⁻¹ * g⁻¹ = x * c₁) (h₂ : g * y * g⁻¹ = y * c₂) :
    x * y * x⁻¹ * y⁻¹ * (x * y * x⁻¹ * y⁻¹) = 1 := by
  set z := x * y * x⁻¹ * y⁻¹ with hzdef
  have hc1 := Subgroup.mem_center_iff.mp hc₁
  have hc2 := Subgroup.mem_center_iff.mp hc₂
  have hzc := Subgroup.mem_center_iff.mp hz
  have hinv : x⁻¹ * y * x * y⁻¹ = z⁻¹ := by
    have : z⁻¹ = y * x * y⁻¹ * x⁻¹ := by rw [hzdef]; group
    calc x⁻¹ * y * x * y⁻¹ = x⁻¹ * (y * x * y⁻¹ * x⁻¹) * x := by group
      _ = x⁻¹ * z⁻¹ * x := by rw [this]
      _ = z⁻¹ := by
          have := (Subgroup.mem_center_iff.mp (inv_mem hz)) x
          calc x⁻¹ * z⁻¹ * x = x⁻¹ * (z⁻¹ * x) := by group
            _ = x⁻¹ * (x * z⁻¹) := by rw [this]
            _ = z⁻¹ := by group
  have hconj : g * (x⁻¹ * y * x * y⁻¹) * g⁻¹ = z := by
    have hx : g * x * g⁻¹ = c₁⁻¹ * x⁻¹ := by
      have : g * x * g⁻¹ = (g * x⁻¹ * g⁻¹)⁻¹ := by group
      rw [this, h₁, _root_.mul_inv_rev]
    calc g * (x⁻¹ * y * x * y⁻¹) * g⁻¹ =
          (g * x⁻¹ * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ := by group
      _ = x * c₁ * (y * c₂) * (c₁⁻¹ * x⁻¹) * (y * c₂)⁻¹ := by rw [h₁, h₂, hx]
      _ = z := by
          have e1 : x * c₁ * (y * c₂) * (c₁⁻¹ * x⁻¹) * (y * c₂)⁻¹ =
              x * (c₁ * (y * (c₂ * (c₁⁻¹ * (x⁻¹ * (c₂⁻¹ * y⁻¹)))))) := by group
          have hc1y : c₁ * y = y * c₁ := (hc1 y).symm
          rw [e1, hzdef]
          have hc2c : c₂ * c₁⁻¹ = c₁⁻¹ * c₂ := (Subgroup.mem_center_iff.mp (inv_mem hc₁) c₂)
          have hc2x : c₂ * x⁻¹ = x⁻¹ * c₂ := (hc2 x⁻¹).symm
          have hc1x : c₁⁻¹ * x⁻¹ = x⁻¹ * c₁⁻¹ := (Subgroup.mem_center_iff.mp (inv_mem hc₁) x⁻¹).symm
          calc x * (c₁ * (y * (c₂ * (c₁⁻¹ * (x⁻¹ * (c₂⁻¹ * y⁻¹)))))) =
                x * (c₁ * y) * (c₂ * c₁⁻¹) * x⁻¹ * c₂⁻¹ * y⁻¹ := by group
            _ = x * (y * c₁) * (c₁⁻¹ * c₂) * x⁻¹ * c₂⁻¹ * y⁻¹ := by rw [hc1y, hc2c]
            _ = x * y * (c₂ * x⁻¹) * c₂⁻¹ * y⁻¹ := by group
            _ = x * y * (x⁻¹ * c₂) * c₂⁻¹ * y⁻¹ := by rw [hc2x]
            _ = x * y * x⁻¹ * y⁻¹ := by group
  rw [hinv] at hconj
  have := (Subgroup.mem_center_iff.mp (inv_mem hz)) g
  have h3 : z⁻¹ = z := by
    calc z⁻¹ = g * z⁻¹ * g⁻¹ := by rw [this]; group
      _ = z := hconj
  calc z * z = z * z⁻¹ := by rw [h3]
    _ = 1 := mul_inv_cancel z

section Diagonal

variable {u : kˣ}

theorem val_inv_eq (hk : Nat.card k = 4) : ((u⁻¹ : kˣ) : k) = u * u := by
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  have h : u * (u * u) = 1 := by rw [← pow_three]; exact h3
  rw [inv_eq_of_mul_eq_one_right h, Units.val_mul]

theorem conjAut_diagGL_aP (x : kˣ) : conjAut 3 k (diagGL x) (aP u) = aP u := by
  rw [aP, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_diagGL, LinearThreeFourOuter.coe_diagGL_inv, hSL, coe_dHom,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm]

theorem conjAut_diagGL_bP (hk : Nat.card k = 4) (hu : u ≠ 1) :
    conjAut 3 k (diagGL u) bP = bP * (aP u)⁻¹ := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hω := val_mul_self_add hk hu
  have hinv := val_inv_eq hk (u := u)
  rw [bP, aP, conjAut_proj, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_diagGL, LinearThreeFourOuter.coe_diagGL_inv,
    Matrix.SpecialLinearGroup.coe_mul, coe_rSL', coe_hSL_inv hk hu, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rM, hiM, Matrix.mul_apply, Fin.sum_univ_three]

theorem conjAut_diagGL_sq_bP (hk : Nat.card k = 4) (hu : u ≠ 1) :
    conjAut 3 k (diagGL (u * u)) bP = bP * (aP u)⁻¹ * (aP u)⁻¹ := by
  rw [← LinearThreeFourOuter.diagGL_mul, map_mul, MulAut.mul_apply, conjAut_diagGL_bP hk hu,
    map_mul, conjAut_diagGL_bP hk hu, map_inv, conjAut_diagGL_aP]

end Diagonal

section Centralizing

variable {u : kˣ}

theorem exists_conjAut_eq_conj (hk : Nat.card k = 4) {A : GL (Fin 3) k}
    (hA : ∀ x ∈ eZero k, conjAut 3 k A x = x) :
    ∃ e ∈ eZero k, conjAut 3 k A = MulAut.conj e := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  set d := Matrix.GeneralLinearGroup.det A
  set A₁ : GL (Fin 3) k := (diagGL d)⁻¹ * A
  have hdet : Matrix.GeneralLinearGroup.det A₁ = 1 := by
    rw [map_mul, map_inv, det_diagGL, inv_mul_cancel]
  let g₁ : Matrix.SpecialLinearGroup (Fin 3) k :=
    ⟨(A₁ : Matrix (Fin 3) (Fin 3) k), by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩
  have hg₁ : Matrix.SpecialLinearGroup.toGL g₁ = A₁ := Units.ext rfl
  have hsplit : conjAut 3 k A = conjAut 3 k (diagGL d) * MulAut.conj (proj 3 k g₁) := by
    rw [← conjAut_toGL, hg₁, ← map_mul, mul_inv_cancel_left]
  set c := conjAut 3 k (diagGL d)
  set y := proj 3 k g₁
  have hfix : ∀ x ∈ eZero k, c (y * x * y⁻¹) = x := fun x hx => by
    have := hA x hx
    rwa [hsplit, MulAut.mul_apply, MulAut.conj_apply] at this
  have hya : y * aP u * y⁻¹ = aP u := by
    have h1 := hfix (aP u) aP_mem_eZero
    have h2 : c (aP u) = aP u := conjAut_diagGL_aP d
    exact c.injective (h1.trans h2.symm)
  have hyE : y ∈ eZero k := by
    rw [← centralizer_aP hk hu, Subgroup.mem_centralizer_singleton_iff]
    calc y * aP u = y * aP u * y⁻¹ * y := by group
      _ = aP u * y := by rw [hya]
  rcases units_eq hk hu d with hd | hd | hd
  · refine ⟨y, hyE, ?_⟩
    rw [hsplit]
    change conjAut 3 k (diagGL d) * MulAut.conj y = MulAut.conj y
    rw [hd, LinearThreeFourOuter.diagGL_one, map_one, one_mul]
  · exfalso
    have h1 := hfix bP bP_mem_eZero
    rw [show y * bP * y⁻¹ = bP by
      rw [commute_of_mem_eZero hk hyE bP_mem_eZero, mul_inv_cancel_right]] at h1
    have h2 : c bP = bP * (aP u)⁻¹ := by
      change conjAut 3 k (diagGL d) bP = _
      rw [hd]
      exact conjAut_diagGL_bP hk hu
    rw [h2, mul_eq_left, inv_eq_one] at h1
    exact aP_ne_one hk hu h1
  · exfalso
    have h1 := hfix bP bP_mem_eZero
    rw [show y * bP * y⁻¹ = bP by
      rw [commute_of_mem_eZero hk hyE bP_mem_eZero, mul_inv_cancel_right]] at h1
    have h2 : c bP = bP * (aP u)⁻¹ * (aP u)⁻¹ := by
      change conjAut 3 k (diagGL d) bP = _
      rw [hd]
      exact conjAut_diagGL_sq_bP hk hu
    rw [h2, mul_assoc, mul_eq_left, ← _root_.mul_inv_rev, inv_eq_one] at h1
    have h3 := pow_three_of_mem_eZero hk (aP_mem_eZero (u := u))
    apply aP_ne_one hk hu
    calc aP u = aP u ^ 3 * (aP u * aP u)⁻¹ := by group
      _ = 1 := by rw [h3, h1]; group

end Centralizing

section Field

variable {u : kˣ} {σ : k ≃+* k}

theorem map_hSL (hk : Nat.card k = 4) (hu : u ≠ 1) (hσ : ∀ a, σ a = a ^ 2) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (hSL u) = (hSL u)⁻¹ := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hω := val_mul_self_add hk hu
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_hSL hk, coe_hSL_inv hk hu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearFieldFour.hM, hiM, hσ]
  all_goals grind

theorem map_rSL : Matrix.SpecialLinearGroup.map σ.toRingHom
    (rSL : Matrix.SpecialLinearGroup (Fin 3) k) = rSL := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_rSL']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rM]

theorem fieldAut_aP (hk : Nat.card k = 4) (hu : u ≠ 1) (hσ : ∀ a, σ a = a ^ 2) :
    fieldAut 3 k σ (aP u) = (aP u)⁻¹ := by
  rw [aP, fieldAut_proj, map_hSL hk hu hσ, map_inv]

theorem fieldAut_bP : fieldAut 3 k σ bP = bP := by
  rw [bP, fieldAut_proj, map_rSL]

theorem hSL_commutator (hk : Nat.card k = 4) :
    hSL u * rSL * (hSL u)⁻¹ * rSL⁻¹ = (zSL u)⁻¹ := by
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  have hrot : dHom (rot (u, 1)) = zSL u * hSL u := by
    rw [zSL, hSL, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · simp only [rot, mul_one, Prod.fst_mul]
      exact inv_eq_of_mul_eq_one_right (show u * (u * u) = 1 by rw [← pow_three]; exact h3)
    · simp [rot]
  have hr : rSL * hSL u = zSL u * hSL u * rSL := by rw [hSL, rSL_mul_dHom, ← hSL, hrot]
  have hz : zSL u ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) k) :=
    scalars_le_center 3 k (zSL_mem_scalars hk)
  have hzc := Subgroup.mem_center_iff.mp hz
  calc hSL u * rSL * (hSL u)⁻¹ * rSL⁻¹ = hSL u * (rSL * hSL u * rSL⁻¹)⁻¹ := by group
    _ = hSL u * (zSL u * hSL u)⁻¹ := by rw [hr, mul_inv_cancel_right]
    _ = (zSL u)⁻¹ := by rw [_root_.mul_inv_rev, mul_inv_cancel_left]

theorem toGL_mem_center {s : Matrix.SpecialLinearGroup (Fin 3) k} (hs : s ∈ scalars 3 k) :
    Matrix.SpecialLinearGroup.toGL s ∈ Subgroup.center (GL (Fin 3) k) := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hs
  rw [Subgroup.mem_center_iff]
  intro B
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hc]
  exact ((Matrix.scalar_commute (c : k) (fun r => Commute.all _ r)
    (B : Matrix (Fin 3) (Fin 3) k)).eq).symm

theorem exists_scalars_of_conjAut {A : GL (Fin 3) k} {g x : Matrix.SpecialLinearGroup (Fin 3) k}
    (h : conjAut 3 k A (proj 3 k g) = proj 3 k x) :
    ∃ s ∈ scalars 3 k, A * Matrix.SpecialLinearGroup.toGL g * A⁻¹ =
      Matrix.SpecialLinearGroup.toGL x * Matrix.SpecialLinearGroup.toGL s := by
  rw [conjAut_proj, proj_eq_proj_iff] at h
  refine ⟨_, inv_mem h, ?_⟩
  rw [← CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, ← map_mul]
  congr 1
  group

theorem not_forall_conjAut_mul_fieldAut (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2)
    (A : GL (Fin 3) k) : ¬ ∀ x ∈ eZero k, (conjAut 3 k A * fieldAut 3 k σ) x = x := by
  intro h
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have ha := h (aP u) aP_mem_eZero
  have hb := h bP bP_mem_eZero
  rw [MulAut.mul_apply, fieldAut_aP hk hu hσ, aP, ← map_inv] at ha
  rw [MulAut.mul_apply, fieldAut_bP, bP] at hb
  obtain ⟨s₁, hs₁, e₁⟩ := exists_scalars_of_conjAut ha
  obtain ⟨s₂, hs₂, e₂⟩ := exists_scalars_of_conjAut hb
  rw [map_inv] at e₁
  have hz : Matrix.SpecialLinearGroup.toGL (hSL u) * Matrix.SpecialLinearGroup.toGL rSL *
      (Matrix.SpecialLinearGroup.toGL (hSL u))⁻¹ * (Matrix.SpecialLinearGroup.toGL rSL)⁻¹ ∈
        Subgroup.center (GL (Fin 3) k) := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hSL_commutator hk]
    exact toGL_mem_center (inv_mem (zSL_mem_scalars hk))
  have key := commutator_mul_self_eq_one hz (toGL_mem_center hs₁) (toGL_mem_center hs₂) e₁ e₂
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hSL_commutator hk, ← map_mul,
    ← map_one Matrix.SpecialLinearGroup.toGL] at key
  have h1 := Matrix.SpecialLinearGroup.toGL_injective key
  rw [← _root_.mul_inv_rev, inv_eq_one, zSL, ← map_mul] at h1
  have h2 := congrFun (congrFun (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k =>
    (g : Matrix (Fin 3) (Fin 3) k)) h1) 0) 0
  simp only [coe_dHom, Matrix.SpecialLinearGroup.coe_one] at h2
  simp at h2
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  apply hu
  have h4 : u * u = 1 := Units.ext (by simpa using h2)
  calc u = u ^ 3 * (u * u)⁻¹ := by group
    _ = 1 := by rw [h3, h4]; group

end Field

section AutCentralizer

variable {σ : k ≃+* k}

abbrev betaAut (σ : k ≃+* k) : MulAut (projectiveSL 3 k) := fieldAut 3 k σ * dualAut 3 k

theorem betaAut_fixed (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) {x : projectiveSL 3 k}
    (hx : x ∈ eZero k) : betaAut σ x = x :=
  beta_fixed hσ hk hx

theorem betaAut_mul_self (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    betaAut σ * betaAut σ = 1 :=
  beta_mul_beta hσ hk

theorem betaAut_ne_one (hk : Nat.card k = 4) : betaAut σ ≠ 1 := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  intro h
  apply LinearThreeFourOuter.conjAut_mul_fieldAut_ne_dualAut 1 σ⁻¹
  rw [map_one, one_mul, map_inv, eq_inv_of_mul_eq_one_right h]

theorem isGraphField_betaAut (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    (stdPinnedPSL 3 k).IsGraphField (betaAut σ) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  rw [betaAut, ← dualAut_mul_fieldAut]
  exact CFSG.RankThree.PartTwo.Sec4.isGraphField_dualAut_mul_fieldAut le_rfl
    (LinearThreeFourOuter.sigma_ne_one hσ hk)

theorem forall_fixes_eZero_iff (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2)
    (α : MulAut (projectiveSL 3 k)) :
    (∀ x ∈ eZero k, α x = x) ↔
      ∃ e ∈ eZero k, α = MulAut.conj e ∨ α = MulAut.conj e * betaAut σ := by
  have hff := LinearThreeFourOuter.fieldAut_sigma_mul_self hσ hk
  have hdd := LinearThreeFourOuter.dualAut_mul_self (k := k)
  have hβinv : ∀ x ∈ eZero k, (betaAut σ)⁻¹ x = x := fun x hx =>
    (betaAut σ).injective (by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply,
      betaAut_fixed hk hσ hx])
  constructor
  · intro h
    obtain ⟨⟨A, a, b⟩, rfl⟩ := LinearThreeFourOuter.exists_nf hσ hk α
    have hAβ : ∀ x ∈ eZero k,
        (LinearThreeFourOuter.nf σ A a b * (betaAut σ)⁻¹) x = x := fun x hx => by
      rw [MulAut.mul_apply, hβinv x hx, h x hx]
    rcases LinearThreeFourOuter.zmod_two_cases a with rfl | rfl <;>
      rcases LinearThreeFourOuter.zmod_two_cases b with rfl | rfl
    · rw [LinearThreeFourOuter.nf_zero_zero] at h ⊢
      obtain ⟨e, he, hAe⟩ := exists_conjAut_eq_conj hk h
      exact ⟨e, he, Or.inl hAe⟩
    · exfalso
      have heq : LinearThreeFourOuter.nf σ A 0 1 * (betaAut σ)⁻¹ =
          conjAut 3 k A * fieldAut 3 k σ := by
        simp only [LinearThreeFourOuter.nf, ZMod.val_zero, pow_zero, mul_one,
          LinearThreeFourOuter.val_one_two, pow_one, betaAut, _root_.mul_inv_rev]
        rw [inv_eq_of_mul_eq_one_right hdd, inv_eq_of_mul_eq_one_right hff, mul_assoc,
          ← mul_assoc (dualAut 3 k), hdd, one_mul]
      exact not_forall_conjAut_mul_fieldAut hk hσ A (heq ▸ hAβ)
    · exfalso
      have heq : LinearThreeFourOuter.nf σ A 1 0 = conjAut 3 k A * fieldAut 3 k σ := by
        simp [LinearThreeFourOuter.nf, LinearThreeFourOuter.val_one_two]
      exact not_forall_conjAut_mul_fieldAut hk hσ A (heq ▸ h)
    · have heq : LinearThreeFourOuter.nf σ A 1 1 * (betaAut σ)⁻¹ = conjAut 3 k A := by
        simp only [LinearThreeFourOuter.nf, LinearThreeFourOuter.val_one_two, pow_one, betaAut]
        group
      obtain ⟨e, he, hAe⟩ := exists_conjAut_eq_conj hk (heq ▸ hAβ)
      refine ⟨e, he, Or.inr ?_⟩
      rw [← hAe, ← heq, inv_mul_cancel_right]
  · rintro ⟨e, he, rfl | rfl⟩ x hx
    · rw [MulAut.conj_apply, commute_of_mem_eZero hk he hx, mul_inv_cancel_right]
    · rw [MulAut.mul_apply, betaAut_fixed hk hσ hx, MulAut.conj_apply,
        commute_of_mem_eZero hk he hx, mul_inv_cancel_right]

theorem conj_injective (hk : Nat.card k = 4) :
    Function.Injective (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  have hc : p ∈ Subgroup.center (projectiveSL 3 k) := by
    rw [Subgroup.mem_center_iff]
    intro q
    have := congrArg (fun α : MulAut (projectiveSL 3 k) => α q) hp
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc q * p = p * q * p⁻¹ * p := by rw [this]
      _ = p * q := by group
  rw [LinearThreeFourOuter.center_projectiveSL_three_eq_bot hk] at hc
  exact hc

theorem eq_one_or_eq_betaAut (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2)
    {α : MulAut (projectiveSL 3 k)} (hfix : ∀ x ∈ eZero k, α x = x) (h3 : ¬ 3 ∣ orderOf α) :
    α = 1 ∨ α = betaAut σ := by
  obtain ⟨e, he, rfl | rfl⟩ := (forall_fixes_eZero_iff hk hσ α).mp hfix
  · by_cases he1 : e = 1
    · left
      rw [he1, map_one]
    · exfalso
      apply h3
      rw [orderOf_injective _ (conj_injective hk) e,
        orderOf_eq_prime (pow_three_of_mem_eZero hk he) he1]
  · by_cases he1 : e = 1
    · right
      rw [he1, map_one, one_mul]
    · exfalso
      have hsq : (MulAut.conj e * betaAut σ) * (MulAut.conj e * betaAut σ) =
          MulAut.conj (e * e) := by
        have hb : betaAut σ * MulAut.conj e * (betaAut σ)⁻¹ = MulAut.conj e := by
          rw [CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, betaAut_fixed hk hσ he]
        calc (MulAut.conj e * betaAut σ) * (MulAut.conj e * betaAut σ) =
              MulAut.conj e * (betaAut σ * MulAut.conj e * (betaAut σ)⁻¹) *
                (betaAut σ * betaAut σ) := by group
          _ = MulAut.conj (e * e) := by rw [hb, betaAut_mul_self hk hσ, mul_one, map_mul]
      have he3 := pow_three_of_mem_eZero hk he
      have h6 : (MulAut.conj e * betaAut σ) ^ 6 = 1 := by
        rw [show 6 = 2 * 3 from rfl, pow_mul, sq, hsq, ← map_pow, ← sq, ← pow_mul,
          show 2 * 3 = 3 * 2 from rfl, pow_mul, he3, one_pow, map_one]
      have hdvd := orderOf_dvd_of_pow_eq_one h6
      have h2 : orderOf (MulAut.conj e * betaAut σ) ∣ 2 := by
        have hcop : Nat.Coprime (orderOf (MulAut.conj e * betaAut σ)) 3 :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3 |>.symm
        exact hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
      have hx2 := orderOf_dvd_iff_pow_eq_one.mp h2
      rw [sq, hsq] at hx2
      have hee : e * e = 1 := conj_injective hk (hx2.trans (map_one _).symm)
      apply he1
      calc e = e ^ 3 * (e * e)⁻¹ := by group
        _ = 1 := by rw [he3, hee]; group

theorem orderOf_betaAut (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2) :
    orderOf (betaAut σ) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact betaAut_mul_self hk hσ) (betaAut_ne_one hk)

theorem eq_bot_or_eq_zpowers_betaAut (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2)
    {X : Subgroup (MulAut (projectiveSL 3 k))} (hX : ¬ 3 ∣ Nat.card X)
    (hfix : ∀ x ∈ X, ∀ e ∈ eZero k, x e = e) :
    X = ⊥ ∨ X = Subgroup.zpowers (betaAut σ) := by
  have hle : X ≤ Subgroup.zpowers (betaAut σ) := by
    intro x hx
    have h3 : ¬ 3 ∣ orderOf x := fun h => hX (h.trans (by
      rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _))
    rcases eq_one_or_eq_betaAut hk hσ (hfix x hx) h3 with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  have hcard : Nat.card (Subgroup.zpowers (betaAut σ)) = 2 := by
    rw [Nat.card_zpowers, orderOf_betaAut hk hσ]
  have hdvd : Nat.card X ∣ 2 := hcard ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · left
    exact Subgroup.eq_bot_of_card_eq X h
  · right
    have : Finite (Subgroup.zpowers (betaAut σ)) := Nat.finite_of_card_ne_zero (by omega)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h])

end AutCentralizer

section Invariant

variable {E : Subgroup (projectiveSL 3 k)} {X : Subgroup (MulAut (projectiveSL 3 k))}

theorem comap_conj_eq_bot (hk : Nat.card k = 4) (hE : Nat.card E = 9) (hX : ¬ 3 ∣ Nat.card X)
    (hEX : ∀ e ∈ E, MulAut.conj e ∈ Subgroup.normalizer (X : Set (MulAut (projectiveSL 3 k)))) :
    X.comap (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)) = ⊥ := by
  refine eq_bot_of_le_normalizer hk hE ?_ ?_
  · intro h
    apply hX
    have h1 : Nat.card ((X.comap (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k))).map
        (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k))) ∣ Nat.card X :=
      Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ X)
    rw [Subgroup.card_map_of_injective (conj_injective hk)] at h1
    exact h.trans h1
  · intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro p
    have h := Subgroup.mem_normalizer_iff.mp (hEX e he) (MulAut.conj p)
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact h

theorem forall_apply_eq_of_invariant (hk : Nat.card k = 4) (hE : Nat.card E = 9)
    (hX : ¬ 3 ∣ Nat.card X)
    (hEX : ∀ e ∈ E, MulAut.conj e ∈ Subgroup.normalizer (X : Set (MulAut (projectiveSL 3 k))))
    {x : MulAut (projectiveSL 3 k)} (hx : x ∈ X) {e : projectiveSL 3 k} (he : e ∈ E) :
    x e = e := by
  have hw : MulAut.conj e * x * (MulAut.conj e)⁻¹ * x⁻¹ ∈ X :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hEX e he) x).mp hx) (inv_mem hx)
  have hw' : MulAut.conj e * x * (MulAut.conj e)⁻¹ * x⁻¹ = MulAut.conj (e * x e⁻¹) := by
    rw [map_mul, ← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, map_inv]
    group
  rw [hw'] at hw
  have hmem : e * x e⁻¹ ∈ X.comap (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)) :=
    hw
  rw [comap_conj_eq_bot hk hE hX hEX, Subgroup.mem_bot, mul_eq_one_iff_eq_inv, map_inv,
    inv_inv] at hmem
  exact hmem.symm

theorem eq_bot_or_eq_zpowers_graphField (hk : Nat.card k = 4) (hE : Nat.card E = 9)
    (hX : ¬ 3 ∣ Nat.card X)
    (hEX : ∀ e ∈ E, MulAut.conj e ∈ Subgroup.normalizer (X : Set (MulAut (projectiveSL 3 k)))) :
    X = ⊥ ∨ ∃ τ : MulAut (projectiveSL 3 k), X = Subgroup.zpowers τ ∧ τ ≠ 1 ∧ τ * τ = 1 ∧
      (stdPinnedPSL 3 k).IsGraphField τ ∧ ∀ e ∈ E, τ e = e := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  have hfixE := fun x (hx : x ∈ X) e (he : e ∈ E) => forall_apply_eq_of_invariant hk hE hX hEX hx he
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_eZero hk hE
  have hX' : ¬ 3 ∣ Nat.card (X.map (MulAut.conj (MulAut.conj g)⁻¹).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj _).injective]
  have hfix' : ∀ x ∈ X.map (MulAut.conj (MulAut.conj g)⁻¹).toMonoidHom, ∀ e ∈ eZero k,
      x e = e := by
    rintro _ ⟨x, hx, rfl⟩ e he
    have h := hfixE x hx (g * e * g⁻¹) ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, MulAut.mul_apply] at h ⊢
    rw [h]
    exact (MulAut.conj g).symm_apply_apply e
  have hXeq : X = (X.map (MulAut.conj (MulAut.conj g)⁻¹).toMonoidHom).map
      (MulAut.conj (MulAut.conj g)).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      exists_exists_and_eq_and]
    constructor
    · intro hy
      exact ⟨y, hy, by group⟩
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1
      group
  rcases eq_bot_or_eq_zpowers_betaAut hk hσ hX' hfix' with h | h
  · left
    rw [hXeq, h, Subgroup.map_bot]
  · right
    set d := MulAut.conj g
    refine ⟨d * betaAut (frobeniusEquiv k 2) * d⁻¹, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hXeq, h, MonoidHom.map_zpowers]
      rfl
    · intro h1
      apply betaAut_ne_one hk (σ := frobeniusEquiv k 2)
      calc betaAut (frobeniusEquiv k 2) =
            d⁻¹ * (d * betaAut (frobeniusEquiv k 2) * d⁻¹) * d := by group
        _ = 1 := by rw [h1]; group
    · calc d * betaAut (frobeniusEquiv k 2) * d⁻¹ * (d * betaAut (frobeniusEquiv k 2) * d⁻¹) =
            d * (betaAut (frobeniusEquiv k 2) * betaAut (frobeniusEquiv k 2)) * d⁻¹ := by group
        _ = 1 := by rw [betaAut_mul_self hk hσ, mul_one, mul_inv_cancel]
    · have hd : d ∈ (stdPinnedPSL 3 k).inndiag := (stdPinnedPSL 3 k).inn_le ⟨g, rfl⟩
      exact PinnedAut.isGraphField_conj _ hd (isGraphField_betaAut hk hσ)
    · rintro _ ⟨e, he, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply]
      rw [MulAut.inv_apply, d.symm_apply_apply]
      exact congrArg d (betaAut_fixed hk hσ he)

end Invariant

section Order

theorem card_mulAut (hk : Nat.card k = 4) : Nat.card (MulAut (projectiveSL 3 k)) = 241920 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨-, hunits, ⟨e, -⟩, -⟩ :=
    LinearThreeFourOuter.linear_three_four_outer_quotient_rank_two_restriction k hk _ hσ
  have hq : Nat.card (MulAut (projectiveSL 3 k) ⧸
      LinearThreeFourOuter.innerAutGroup (projectiveSL 3 k)) = 12 := by
    rw [Nat.card_congr e.toEquiv, SemidirectProduct.card, hunits, Nat.card_prod]
    simp
  have hinn : Nat.card (LinearThreeFourOuter.innerAutGroup (projectiveSL 3 k)) = 20160 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (conj_injective hk)).toEquiv,
      card_projectiveSL hk]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (LinearThreeFourOuter.innerAutGroup (projectiveSL 3 k)), hq, hinn]

theorem pRank_three_mulAut (hk : Nat.card k = 4) :
    CFSG.pRank 3 (MulAut (projectiveSL 3 k)) = 2 := by
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  set x := conjAut 3 k (diagGL u)
  set y := (MulAut.conj (bP : projectiveSL 3 k) : MulAut (projectiveSL 3 k))
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  have hx3 : x ^ 3 = 1 := by
    rw [← map_pow, pow_three, LinearThreeFourOuter.diagGL_mul, LinearThreeFourOuter.diagGL_mul,
      ← pow_three, h3, LinearThreeFourOuter.diagGL_one, map_one]
  have hy3 : y ^ 3 = 1 := by
    rw [← map_pow, pow_three_of_mem_eZero hk bP_mem_eZero, map_one]
  have hab : aP u * bP = bP * aP u := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  have hxa : x (aP u)⁻¹ = (aP u)⁻¹ := by rw [map_inv, conjAut_diagGL_aP]
  have hz : ⁅x, y⁆ = MulAut.conj (aP u)⁻¹ := by
    rw [commutatorElement_def, CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv,
      conjAut_diagGL_bP hk hu, ← map_inv, ← map_mul]
    congr 1
    calc bP * (aP u)⁻¹ * bP⁻¹ = bP * ((aP u)⁻¹ * bP⁻¹) := by group
      _ = bP * (bP⁻¹ * (aP u)⁻¹) := by
          rw [show (aP u)⁻¹ * bP⁻¹ = (bP * aP u)⁻¹ by group, ← hab]
          group
      _ = (aP u)⁻¹ := by group
  have hzx : Commute ⁅x, y⁆ x := by
    rw [hz]
    show MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹
    have := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv x (aP u)⁻¹
    rw [hxa] at this
    calc MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹ * x⁻¹ * x := by rw [this]
      _ = x * MulAut.conj (aP u)⁻¹ := by group
  have hzy : Commute ⁅x, y⁆ y := by
    rw [hz]
    show MulAut.conj (aP u)⁻¹ * MulAut.conj bP = MulAut.conj bP * MulAut.conj (aP u)⁻¹
    rw [← map_mul, ← map_mul]
    congr 1
    calc (aP u)⁻¹ * bP = (aP u)⁻¹ * (bP * aP u) * (aP u)⁻¹ := by group
      _ = (aP u)⁻¹ * (aP u * bP) * (aP u)⁻¹ := by rw [hab]
      _ = bP * (aP u)⁻¹ := by group
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    rw [hz]
    intro h
    exact aP_ne_one hk hu (inv_eq_one.mp (conj_injective hk (h.trans (map_one _).symm)))
  have hL : (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 = 3 := by
    rw [card_mulAut hk]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 241920 = 3 ^ 3 * 8960 by norm_num) (by norm_num)
  exact CFSG.RankThree.Asc83Table.ex27_pRank hx3 hy3 hzx hzy hz1 hL

theorem pRank_three_mulAut_of_mulEquiv (hk : Nat.card k = 4) {H : Type*} [Group H]
    (e : H ≃* projectiveSL 3 k) : CFSG.pRank 3 (MulAut H) = 2 := by
  rw [CFSG.RankThree.Asc83Table.pRank_congr (MulAut.congr e), pRank_three_mulAut hk]

end Order

section Involutions

variable {k : Type} [Field k] [Finite k] {σ : k ≃+* k}

theorem involution_cases (hk : Nat.card k = 4) (hσ : ∀ a, σ a = a ^ 2)
    {α : MulAut (projectiveSL 3 k)} (hα : α * α = 1) :
    α ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∨
      ∃ H : GL (Fin 3) k, α = conjAut 3 k H * fieldAut 3 k σ * (conjAut 3 k H)⁻¹ ∨
        α = conjAut 3 k H * dualAut 3 k * (conjAut 3 k H)⁻¹ ∨
        α = conjAut 3 k H * betaAut σ * (conjAut 3 k H)⁻¹ := by
  have hσ1 := LinearThreeFourOuter.sigma_ne_one hσ hk
  have hk' : Nat.card k = 2 ^ 2 := by rw [hk]; norm_num
  obtain ⟨⟨A, a, b⟩, rfl⟩ := LinearThreeFourOuter.exists_nf hσ hk α
  have hα2 : LinearThreeFourOuter.nf σ A a b ^ 2 = 1 := by rw [sq]; exact hα
  rcases LinearThreeFourOuter.zmod_two_cases a with rfl | rfl <;>
    rcases LinearThreeFourOuter.zmod_two_cases b with rfl | rfl
  · left
    rw [LinearThreeFourOuter.nf_zero_zero] at hα ⊢
    rw [← map_mul, ← LinearThreeFourOuter.nf_zero_zero σ] at hα
    obtain ⟨hdet, -, -⟩ := LinearThreeFourOuter.nf_eq_one hσ hk hα
    rw [map_mul] at hdet
    have h3 := LinearThreeFourOuter.units_pow_three hk (Matrix.GeneralLinearGroup.det A)
    rw [LinearThreeFourOuter.conjAut_mem_range_conj_iff hk]
    calc Matrix.GeneralLinearGroup.det A =
          Matrix.GeneralLinearGroup.det A ^ 3 *
            (Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det A)⁻¹ := by group
      _ = 1 := by rw [h3, hdet]; group
  · right
    simp only [LinearThreeFourOuter.nf, ZMod.val_zero, LinearThreeFourOuter.val_one_two,
      pow_zero, pow_one, mul_one] at hα2 ⊢
    obtain ⟨-, ⟨H, C, -, hHC, hC⟩, -⟩ :=
      UnitaryHigher.even_linear_pure_graph_involution_normal_forms (by norm_num) hk' le_rfl A hα2
    rcases hC with ⟨hC1, -⟩ | ⟨r, hr, -⟩
    · have hC1' : C = 1 := Units.ext hC1
      refine ⟨H, Or.inr (Or.inl ?_)⟩
      rw [hHC, hC1', map_one, one_mul]
    · omega
  · right
    simp only [LinearThreeFourOuter.nf, ZMod.val_zero, LinearThreeFourOuter.val_one_two,
      pow_zero, pow_one, mul_one] at hα2 ⊢
    obtain ⟨-, -, H, hH⟩ :=
      even_linear_field_involution_descent (f := 2) (by norm_num) hk' le_rfl A σ hσ1 hα2
    exact ⟨H, Or.inl hH⟩
  · right
    simp only [LinearThreeFourOuter.nf, LinearThreeFourOuter.val_one_two, pow_one] at hα2 ⊢
    obtain ⟨-, -, H, hH⟩ := odd_linear_graph_field_involution_conjugacy Nat.prime_two
      (f := 2) (by norm_num) hk' le_rfl A σ hσ1 hα2
    exact ⟨H, Or.inr (Or.inr hH)⟩

end Involutions


end CFSG.RankThree.PartTwo.KFacts.L34
