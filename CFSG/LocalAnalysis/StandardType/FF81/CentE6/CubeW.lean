module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatJ

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG.RankThree.GF2n.Smith81
open exteriorPower

private theorem cubeAct_mul (g h : SL(6, ZMod 2)) :
    cubeAct (g * h) = cubeAct g * cubeAct h := by
  change TauCeti.extPowerRep (ZMod 2) 6 3 (Matrix.SpecialLinearGroup.toGL (g * h)) =
    TauCeti.extPowerRep (ZMod 2) 6 3 (Matrix.SpecialLinearGroup.toGL g) *
      TauCeti.extPowerRep (ZMod 2) 6 3 (Matrix.SpecialLinearGroup.toGL h)
  rw [show (Matrix.SpecialLinearGroup.toGL (g * h)) =
      Matrix.SpecialLinearGroup.toGL g * Matrix.SpecialLinearGroup.toGL h from map_mul _ _ _]
  rw [map_mul]

private theorem cubeAct_one : cubeAct (1 : SL(6, ZMod 2)) = 1 := by
  change TauCeti.extPowerRep (ZMod 2) 6 3 (Matrix.SpecialLinearGroup.toGL (1 : SL(6, ZMod 2))) =
    (1 : A5Cube.Cube (ZMod 2) →ₗ[ZMod 2] A5Cube.Cube (ZMod 2))
  rw [show (Matrix.SpecialLinearGroup.toGL (1 : SL(6, ZMod 2))) =
      (1 : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) from map_one _]
  rw [map_one]

private def cubeAlt : AlternatingMap (ZMod 2) (Fin 6 → ZMod 2) (A5Cube.Cube (ZMod 2)) (Fin 3) :=
  @exteriorPower.ιMulti (ZMod 2) (inferInstance : CommRing (ZMod 2)) 3 (Fin 6 → ZMod 2)
    (inferInstance : AddCommGroup (Fin 6 → ZMod 2))
    (inferInstance : Module (ZMod 2) (Fin 6 → ZMod 2))

private def u (v : Fin 3 → Fin 6) : A5Cube.Cube (ZMod 2) :=
  ιMulti (ZMod 2) 3 (A5Cube.e (ZMod 2) ∘ v)

private def alt (w : Fin 3 → Fin 6 → ZMod 2) : A5Cube.Cube (ZMod 2) :=
  ιMulti (ZMod 2) 3 w

private theorem u_eq_zero_of_not_injective (v : Fin 3 → Fin 6)
    (h : ¬ Function.Injective v) : u v = 0 := by
  rw [Function.Injective] at h
  push Not at h
  obtain ⟨a, b, hab, hne⟩ := h
  have hcomp : (A5Cube.e (ZMod 2) ∘ v) a = (A5Cube.e (ZMod 2) ∘ v) b :=
    congrArg (A5Cube.e (ZMod 2)) hab
  have hz := AlternatingMap.map_eq_zero_of_eq cubeAlt (A5Cube.e (ZMod 2) ∘ v)
    (i := a) (j := b) hcomp hne
  rw [u]
  exact hz

private theorem u_update_zero_eq_zero (v : Fin 3 → Fin 6) (t0 t1 : Fin 3)
    (h : t1 ≠ t0) (ht1 : v t1 = 0) : u (Function.update v t0 0) = 0 := by
  have heq : (A5Cube.e (ZMod 2) ∘ Function.update v t0 0) t0 =
      (A5Cube.e (ZMod 2) ∘ Function.update v t0 0) t1 := by
    rw [Function.comp_apply, Function.comp_apply, Function.update_self,
      Function.update_of_ne h, ht1]
  have hz := AlternatingMap.map_eq_zero_of_eq cubeAlt
    (A5Cube.e (ZMod 2) ∘ Function.update v t0 0) (i := t0) (j := t1) heq (Ne.symm h)
  rw [u]
  exact hz

private theorem coe_elem (i j : Fin 6) (hij : i ≠ j) :
    (elem i j : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 + Matrix.single i j 1 := by
  unfold elem
  rw [dif_neg hij]
  exact Matrix.SpecialLinearGroup.transvection_coe hij 1

private theorem cubeAct_elem_u (i j : Fin 6) (hij : i ≠ j) (v : Fin 3 → Fin 6)
    (t0 : Fin 3) (ht0 : v t0 = j) (huniq : ∀ t, v t = j → t = t0) :
    cubeAct (elem i j) (u v) = u v + u (Function.update v t0 i) := by
  have hfun : (fun t => (↑(Matrix.SpecialLinearGroup.toGL (elem i j)) :
        Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
        ((A5Cube.e (ZMod 2) ∘ v) t)) =
      Function.update (A5Cube.e (ZMod 2) ∘ v) t0
        (A5Cube.e (ZMod 2) j + A5Cube.e (ZMod 2) i) := by
    funext t
    rw [show (↑(Matrix.SpecialLinearGroup.toGL (elem i j)) :
        Matrix (Fin 6) (Fin 6) (ZMod 2)) = (elem i j : Matrix (Fin 6) (Fin 6) (ZMod 2))
        from Matrix.SpecialLinearGroup.coe_GL_coe_matrix _]
    by_cases ht : t = t0
    · subst ht
      rw [Function.comp_apply, Function.update_self, ht0, coe_elem i j hij, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec_eq]
      simp [A5Cube.e, mul_one]
    · rw [Function.comp_apply, Function.update_of_ne ht]
      have hvj : v t ≠ j := fun h => ht (huniq t h)
      rw [coe_elem i j hij, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
      simp [A5Cube.e, hvj]
  rw [u, cubeAct, A5Cube.rho_ιMulti, hfun]
  rw [AlternatingMap.map_update_add]
  congr 1
  · rw [show A5Cube.e (ZMod 2) j = (A5Cube.e (ZMod 2) ∘ v) t0 from by
      rw [Function.comp_apply, ht0]]
    rw [Function.update_eq_self t0 (A5Cube.e (ZMod 2) ∘ v)]
  · rw [u, Function.comp_update]

private theorem cubeAct_elem_u_of_notMem (i j : Fin 6) (hij : i ≠ j) (v : Fin 3 → Fin 6)
    (h : ∀ t, v t ≠ j) : cubeAct (elem i j) (u v) = u v := by
  have hfun : (fun t => (↑(Matrix.SpecialLinearGroup.toGL (elem i j)) :
        Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
        ((A5Cube.e (ZMod 2) ∘ v) t)) = (A5Cube.e (ZMod 2) ∘ v) := by
    funext t
    rw [show (↑(Matrix.SpecialLinearGroup.toGL (elem i j)) :
        Matrix (Fin 6) (Fin 6) (ZMod 2)) = (elem i j : Matrix (Fin 6) (Fin 6) (ZMod 2))
        from Matrix.SpecialLinearGroup.coe_GL_coe_matrix _]
    rw [Function.comp_apply, coe_elem i j hij, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec_eq]
    simp [A5Cube.e, h t]
  rw [u, cubeAct, A5Cube.rho_ιMulti, hfun]

private theorem elem_zero_five : elem (0 : Fin 6) 5 = CFSG.Holt.SL6.stdTransvection := by
  unfold elem CFSG.Holt.SL6.stdTransvection
  rw [dif_neg (show (0 : Fin 6) ≠ 5 by decide)]

private def Good (v : Fin 3 → Fin 6) : Prop :=
  (∀ t, v t ≠ 5) ∧ ∃ t, v t = 0

private def P : Submodule (ZMod 2) (A5Cube.Cube (ZMod 2)) :=
  Submodule.span (ZMod 2) {x | ∃ v : Fin 3 → Fin 6, Good v ∧ x = u v}

private theorem u_mem_P {v : Fin 3 → Fin 6} (hv : Good v) : u v ∈ P :=
  Submodule.subset_span ⟨v, hv, rfl⟩

private theorem cubeAct_t1_u (v : Fin 3 → Fin 6) (t0 : Fin 3) (ht0 : v t0 = 5)
    (huniq : ∀ t, v t = 5 → t = t0) :
    cubeAct CFSG.Holt.SL6.stdTransvection (u v) = u v + u (Function.update v t0 0) := by
  rw [← elem_zero_five]
  exact cubeAct_elem_u 0 5 (by decide) v t0 ht0 huniq

private theorem cubeAct_t1_u_of_notMem (v : Fin 3 → Fin 6) (h : ∀ t, v t ≠ 5) :
    cubeAct CFSG.Holt.SL6.stdTransvection (u v) = u v := by
  rw [← elem_zero_five]
  exact cubeAct_elem_u_of_notMem 0 5 (by decide) v h

private theorem Good_update (v : Fin 3 → Fin 6) (t0 : Fin 3)
    (huniq : ∀ t, v t = 5 → t = t0) : Good (Function.update v t0 0) := by
  refine ⟨fun t => ?_, ⟨t0, by simp⟩⟩
  by_cases ht : t = t0
  · subst ht; simp
  · rw [Function.update_of_ne ht]
    intro hvt
    exact absurd (huniq t hvt) ht

private theorem t1_sub_u_mem_P (v : Fin 3 → Fin 6) :
    (cubeAct CFSG.Holt.SL6.stdTransvection - 1) (u v) ∈ P := by
  change cubeAct CFSG.Holt.SL6.stdTransvection (u v) - u v ∈ P
  by_cases h5 : ∃ t, v t = 5
  · by_cases hinj : Function.Injective v
    · obtain ⟨t0, ht0⟩ := h5
      have huniq : ∀ t, v t = 5 → t = t0 := fun t ht => hinj (ht.trans ht0.symm)
      rw [cubeAct_t1_u v t0 ht0 huniq]
      have hsub : u v + u (Function.update v t0 0) - u v = u (Function.update v t0 0) := by abel
      rw [hsub]
      exact u_mem_P (Good_update v t0 huniq)
    · rw [u_eq_zero_of_not_injective v hinj]
      simp
  · rw [cubeAct_t1_u_of_notMem v (fun t ht => h5 ⟨t, ht⟩)]
    simp

private theorem cubeBasis_eq_u (I : Set.powersetCard (Fin 6) 3) :
    A5Cube.cubeBasis (ZMod 2) I = u (A5Cube.enum I) := by
  rw [u, A5Cube.cubeBasis, exteriorPower.basis_apply]
  simp only [exteriorPower.ιMulti_family, A5Cube.enum]
  congr 1
  funext t
  simp [A5Cube.e, Pi.basisFun_apply]

private theorem Wsp_le_P : Wsp ≤ P := by
  intro w hw
  obtain ⟨x, rfl⟩ := hw
  have hx : x ∈ Submodule.span (ZMod 2) (Set.range (A5Cube.cubeBasis (ZMod 2))) := by
    rw [(A5Cube.cubeBasis (ZMod 2)).span_eq]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun x _ => (cubeAct CFSG.Holt.SL6.stdTransvection - 1) x ∈ P) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨I, rfl⟩
    rw [cubeBasis_eq_u]
    exact t1_sub_u_mem_P (A5Cube.enum I)
  · simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact P.add_mem ha hb
  · intro c a _ ha
    rw [map_smul]
    exact P.smul_mem c ha

private noncomputable def Fix (s : SL(6, ZMod 2)) : Submodule (ZMod 2) (A5Cube.Cube (ZMod 2)) :=
  LinearMap.ker (cubeAct s - 1)

private theorem mem_Fix {s : SL(6, ZMod 2)} {x : A5Cube.Cube (ZMod 2)} :
    x ∈ Fix s ↔ cubeAct s x = x := by
  rw [Fix, LinearMap.mem_ker]
  change cubeAct s x - x = 0 ↔ cubeAct s x = x
  rw [sub_eq_zero]

private theorem u_mem_fix_elem_0_j {j : Fin 6} (hj : j ≠ 0) {v : Fin 3 → Fin 6}
    (hv : Good v) : u v ∈ Fix (elem 0 j) := by
  rw [mem_Fix]
  by_cases hinj : Function.Injective v
  · by_cases hmem : j ∈ Set.range v
    · obtain ⟨t0, ht0⟩ := hmem
      have huniq : ∀ t, v t = j → t = t0 := fun t ht => hinj (ht.trans ht0.symm)
      rw [cubeAct_elem_u 0 j (Ne.symm hj) v t0 ht0 huniq]
      obtain ⟨t1, ht1⟩ := hv.2
      have hne : t1 ≠ t0 := by
        intro h
        rw [h] at ht1
        exact hj (ht0.symm.trans ht1)
      rw [u_update_zero_eq_zero v t0 t1 hne ht1, add_zero]
    · rw [cubeAct_elem_u_of_notMem 0 j (Ne.symm hj) v (fun t ht => hmem ⟨t, ht⟩)]
  · rw [u_eq_zero_of_not_injective v hinj]
    exact map_zero _

private theorem u_mem_fix_elem_i_5 {i : Fin 6} (hi : i ≠ 5) {v : Fin 3 → Fin 6}
    (hv : Good v) : u v ∈ Fix (elem i 5) := by
  rw [mem_Fix]
  rw [cubeAct_elem_u_of_notMem i 5 hi v (fun t ht => hv.1 t ht)]

private theorem P_le_fix_elem_0_j {j : Fin 6} (hj : j ≠ 0) : P ≤ Fix (elem 0 j) := by
  rw [P, Submodule.span_le]
  rintro x ⟨v, hv, rfl⟩
  exact u_mem_fix_elem_0_j hj hv

private theorem P_le_fix_elem_i_5 {i : Fin 6} (hi : i ≠ 5) : P ≤ Fix (elem i 5) := by
  rw [P, Submodule.span_le]
  rintro x ⟨v, hv, rfl⟩
  exact u_mem_fix_elem_i_5 hi hv

private def Ksub : Subgroup SL(6, ZMod 2) where
  carrier := {g | ∀ w ∈ Wsp, cubeAct g w = w}
  one_mem' := by intro w hw; rw [cubeAct_one]; rfl
  mul_mem' := by
    intro g h hg hh w hw
    rw [cubeAct_mul]
    change cubeAct g (cubeAct h w) = w
    rw [hh w hw, hg w hw]
  inv_mem' := by
    intro g hg w hw
    have h2 : cubeAct g⁻¹ (cubeAct g w) = cubeAct g⁻¹ w := by rw [hg w hw]
    have h3 : cubeAct g⁻¹ (cubeAct g w) = w := by
      change (cubeAct g⁻¹ * cubeAct g) w = w
      rw [← cubeAct_mul, inv_mul_cancel, cubeAct_one]
      rfl
    rw [h3] at h2
    exact h2.symm

private theorem Sgrp_le_Ksub : Sgrp ≤ Ksub := by
  rw [Sgrp, sup_le_iff]
  constructor
  · rw [Sone, Subgroup.closure_le]
    rintro g ⟨j, hj, rfl⟩
    intro w hw
    exact mem_Fix.mp (P_le_fix_elem_0_j (fun h => by rw [h] at hj; simp at hj)
      (Wsp_le_P hw))
  · rw [Ssix, Subgroup.closure_le]
    rintro g ⟨i, hi, rfl⟩
    intro w hw
    exact mem_Fix.mp (P_le_fix_elem_i_5 (fun h => by rw [h] at hi; simp at hi)
      (Wsp_le_P hw))

private def FixVec (x : Fin 6 → ZMod 2) : Subgroup SL(6, ZMod 2) where
  carrier := {g | (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hh, hg]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h2 : (↑(g⁻¹) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
        ((↑g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    calc (↑(g⁻¹) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec x
        = (↑(g⁻¹) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            ((↑g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec x) := by rw [hg]
      _ = x := h2

private def M0 : Submodule (ZMod 2) (Fin 6 → ZMod 2) where
  carrier := {x | x 0 = 0 ∧ x 5 = 0}
  add_mem' := by intro a b ha hb; exact ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := by intro c a ha; exact ⟨by simp [ha.1], by simp [ha.2]⟩

private def mid (i : Fin 4) : Fin 6 := ⟨i.val + 1, by omega⟩

private theorem mid_ne_zero (i : Fin 4) : mid i ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp [mid] at this

private theorem mid_ne_five (i : Fin 4) : mid i ≠ 5 := by
  intro h; have := congrArg Fin.val h; simp [mid] at this; omega

private theorem mem_M0_iff {x : Fin 6 → ZMod 2} : x ∈ M0 ↔ x 0 = 0 ∧ x 5 = 0 := Iff.rfl

private theorem e_mid_mem_M0 (i : Fin 4) : A5Cube.e (ZMod 2) (mid i) ∈ M0 := by
  refine (mem_M0_iff (x := A5Cube.e (ZMod 2) (mid i))).mpr ⟨?_, ?_⟩ <;>
    simp [A5Cube.e, mid_ne_zero i, mid_ne_five i]

private def StabM0 : Subgroup SL(6, ZMod 2) where
  carrier := {g | ∀ x, x ∈ M0 ↔ (Matrix.SpecialLinearGroup.toLin' g) x ∈ M0}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [map_mul, LinearEquiv.mul_apply]
    exact (hh x).trans (hg _)
  inv_mem' := by
    intro g hg x
    simp only [Set.mem_setOf_eq] at hg ⊢
    rw [map_inv]
    have hInv :
        (Matrix.SpecialLinearGroup.toLin' g) ((Matrix.SpecialLinearGroup.toLin' g)⁻¹ x) = x := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    exact ((hg ((Matrix.SpecialLinearGroup.toLin' g)⁻¹ x)).trans
      (iff_of_eq (congrArg (fun z => z ∈ M0) hInv))).symm

private theorem generator_mem_FixVec_zero (i j : Fin 6) (hij : i ≠ j) (hj : 1 ≤ j.val) :
    elem i j ∈ FixVec (A5Cube.e (ZMod 2) 0) := by
  change (elem i j : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (A5Cube.e (ZMod 2) 0)
    = A5Cube.e (ZMod 2) 0
  rw [coe_elem i j hij, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  rw [show (A5Cube.e (ZMod 2) 0) j = 0 from by
    simp [A5Cube.e, show j ≠ 0 from fun h => by rw [h] at hj; simp at hj]]
  simp

private theorem generator_mem_FixVec_five (i j : Fin 6) (hij : i ≠ j) (hj : j.val ≤ 4) :
    elem i j ∈ FixVec (A5Cube.e (ZMod 2) 5) := by
  change (elem i j : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (A5Cube.e (ZMod 2) 5)
    = A5Cube.e (ZMod 2) 5
  rw [coe_elem i j hij, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  rw [show (A5Cube.e (ZMod 2) 5) j = 0 from by
    simp [A5Cube.e, show j ≠ 5 from fun h => by rw [h] at hj; simp at hj]]
  simp

private theorem generator_mem_StabM0 (i j : Fin 6) (hij : i ≠ j)
    (hi1 : 1 ≤ i.val) (hi4 : i.val ≤ 4) : elem i j ∈ StabM0 := by
  intro x
  change x ∈ M0 ↔ (Matrix.SpecialLinearGroup.toLin' (elem i j)) x ∈ M0
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  rw [coe_elem i j hij, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  simp only [one_mul]
  have hei : Pi.single i (1 : ZMod 2) ∈ M0 := by
    refine (mem_M0_iff (x := Pi.single i (1 : ZMod 2))).mpr ⟨?_, ?_⟩ <;>
      simp [show i ≠ 0 from fun h => by rw [h] at hi1; simp at hi1,
        show i ≠ 5 from fun h => by rw [h] at hi4; simp at hi4]
  constructor
  · intro hx
    exact M0.add_mem hx (M0.smul_mem _ hei)
  · intro hx
    have h2 : (x j • Pi.single i (1 : ZMod 2)) ∈ M0 := M0.smul_mem _ hei
    have h3 := M0.sub_mem hx h2
    have h4 : x + x j • Pi.single i (1 : ZMod 2) - x j • Pi.single i (1 : ZMod 2) = x := by
      abel
    exact h4 ▸ h3

private theorem Jgrp_le_FixVec_zero : Jgrp ≤ FixVec (A5Cube.e (ZMod 2) 0) := by
  rw [Jgrp, Subgroup.closure_le]
  rintro g ⟨i, j, hij, hi1, hi4, hj1, hj4, rfl⟩
  exact generator_mem_FixVec_zero i j hij hj1

private theorem Jgrp_le_FixVec_five : Jgrp ≤ FixVec (A5Cube.e (ZMod 2) 5) := by
  rw [Jgrp, Subgroup.closure_le]
  rintro g ⟨i, j, hij, hi1, hi4, hj1, hj4, rfl⟩
  exact generator_mem_FixVec_five i j hij hj4

private theorem Jgrp_le_StabM0 : Jgrp ≤ StabM0 := by
  rw [Jgrp, Subgroup.closure_le]
  rintro g ⟨i, j, hij, hi1, hi4, hj1, hj4, rfl⟩
  exact generator_mem_StabM0 i j hij hi1 hi4

private theorem u_middle_mem_Wsp (i k : Fin 4) :
    u ![0, mid i, mid k] ∈ Wsp := by
  have ht0 : (![5, mid i, mid k] : Fin 3 → Fin 6) 0 = 5 := rfl
  have huniq : ∀ t : Fin 3, (![5, mid i, mid k] : Fin 3 → Fin 6) t = 5 → t = 0 := by
    intro t ht; fin_cases t <;> simp_all [mid_ne_five]
  have hact := cubeAct_t1_u ![5, mid i, mid k] 0 ht0 huniq
  rw [show Function.update (![5, mid i, mid k] : Fin 3 → Fin 6) 0 0 = ![0, mid i, mid k] from by
    funext t; fin_cases t <;> simp] at hact
  refine ⟨u ![5, mid i, mid k], ?_⟩
  change cubeAct CFSG.Holt.SL6.stdTransvection (u ![5, mid i, mid k])
    - u ![5, mid i, mid k] = u ![0, mid i, mid k]
  rw [hact]
  abel

private theorem mid_injective : Function.Injective mid := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; simp [mid] at this; omega

private theorem mid_eq_iff {i j : Fin 4} : mid i = mid j ↔ i = j :=
  mid_injective.eq_iff

private def cv (j : SL(6, ZMod 2)) (i : Fin 4) : Fin 6 → ZMod 2 :=
  (j : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (A5Cube.e (ZMod 2) (mid i))

private def ym (j : SL(6, ZMod 2)) (i : Fin 4) (a : Fin 4) : ZMod 2 :=
  cv j i (mid a)

private def tri (a b : Fin 4) (hab : a < b) : Fin 3 ↪o Fin 6 :=
  OrderEmbedding.ofStrictMono ![0, mid a, mid b] (by
    have hab' : (a : ℕ) < (b : ℕ) := hab
    intro s t hst
    fin_cases s <;> fin_cases t <;> simp [mid] at hst ⊢
    · change 0 < (a : ℕ) + 1; omega
    · change 0 < (b : ℕ) + 1; omega
    · exact hab
)

private def I3 (a b : Fin 4) (hab : a < b) : Set.powersetCard (Fin 6) 3 :=
  Set.powersetCard.ofFinEmbEquiv (tri a b hab)

private theorem enum_I3 (a b : Fin 4) (hab : a < b) :
    A5Cube.enum (I3 a b hab) = tri a b hab := by
  rw [I3, A5Cube.enum, Equiv.symm_apply_apply]

private theorem ym_mem_M0 {j : SL(6, ZMod 2)} (hj : j ∈ Jgrp) (i : Fin 4) :
    (j : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (A5Cube.e (ZMod 2) (mid i)) ∈ M0 := by
  have hx := (Jgrp_le_StabM0 hj (A5Cube.e (ZMod 2) (mid i))).mp (e_mid_mem_M0 i)
  rwa [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply] at hx

private theorem jj_fix_zero {j : SL(6, ZMod 2)} (hj : j ∈ Jgrp) :
    (j : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (A5Cube.e (ZMod 2) 0) = A5Cube.e (ZMod 2) 0 :=
  Jgrp_le_FixVec_zero hj

private theorem eq_triple_of_mem_J {j : SL(6, ZMod 2)} (hj : j ∈ Jgrp)
    (h : ∀ w ∈ Wsp, cubeAct j w = w) (i k : Fin 4) :
    alt ![A5Cube.e (ZMod 2) 0, cv j i, cv j k] =
      alt ![A5Cube.e (ZMod 2) 0, A5Cube.e (ZMod 2) (mid i), A5Cube.e (ZMod 2) (mid k)] := by
  have hv := h (u ![0, mid i, mid k]) (u_middle_mem_Wsp i k)
  have hfun : (fun t : Fin 3 => (j : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
      ((A5Cube.e (ZMod 2) ∘ (![0, mid i, mid k] : Fin 3 → Fin 6)) t)) =
      ![A5Cube.e (ZMod 2) 0, cv j i, cv j k] := by
    funext t; fin_cases t <;> simp [cv, jj_fix_zero hj]
  have heq : (A5Cube.e (ZMod 2) ∘ (![0, mid i, mid k] : Fin 3 → Fin 6)) =
      ![A5Cube.e (ZMod 2) 0, A5Cube.e (ZMod 2) (mid i), A5Cube.e (ZMod 2) (mid k)] := by
    funext t; fin_cases t <;> simp
  simp only [u] at hv
  rw [cubeAct, A5Cube.rho_ιMulti] at hv
  rw [show (↑(Matrix.SpecialLinearGroup.toGL j) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      (j : Matrix (Fin 6) (Fin 6) (ZMod 2)) from
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix _] at hv
  rw [hfun, heq] at hv
  simpa only [alt] using hv

private theorem minor_eq {j : SL(6, ZMod 2)} (hj : j ∈ Jgrp)
    (h : ∀ w ∈ Wsp, cubeAct j w = w) (i k : Fin 4) (a b : Fin 4) (hab : a < b) :
    ym j i a * ym j k b - ym j i b * ym j k a =
      (if i = a then 1 else 0) * (if k = b then 1 else 0) -
      (if i = b then 1 else 0) * (if k = a then 1 else 0) := by
  have hc := congrArg (fun ξ => A5Cube.coord (ZMod 2) ξ (I3 a b hab))
    (eq_triple_of_mem_J hj h i k)
  have htri : ∀ t : Fin 3, (tri a b hab) t = (![0, mid a, mid b] : Fin 3 → Fin 6) t :=
    fun t => rfl
  simp only [alt, A5Cube.coord_ιMulti, enum_I3] at hc
  rw [Matrix.det_fin_three, Matrix.det_fin_three] at hc
  simp [htri, cv, A5Cube.e, Pi.single_apply, mid_eq_iff, mid_ne_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  simpa [ym, cv, eq_comm, mul_comm] using hc

private theorem exists_ne_two : ∀ i a : Fin 4, i ≠ a → ∃ k : Fin 4, k ≠ i ∧ k ≠ a := by
  decide

private theorem minor_eq_all {j : SL(6, ZMod 2)} (hj : j ∈ Jgrp)
    (h : ∀ w ∈ Wsp, cubeAct j w = w) (i k a b : Fin 4) :
    ym j i a * ym j k b - ym j i b * ym j k a =
      (if i = a then 1 else 0) * (if k = b then 1 else 0) -
      (if i = b then 1 else 0) * (if k = a then 1 else 0) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact minor_eq hj h i k a b hab
  · simp
  · have h1 := minor_eq hj h i k b a hba
    calc ym j i a * ym j k b - ym j i b * ym j k a
        = ym j i b * ym j k a - ym j i a * ym j k b := by
          simp only [sub_eq_add_neg, CharTwo.neg_eq]; abel
      _ = (if i = b then 1 else 0) * (if k = a then 1 else 0) -
          (if i = a then 1 else 0) * (if k = b then 1 else 0) := h1
      _ = (if i = a then 1 else 0) * (if k = b then 1 else 0) -
          (if i = b then 1 else 0) * (if k = a then 1 else 0) := by
          simp only [sub_eq_add_neg, CharTwo.neg_eq]; abel

private theorem ym_offdiag {j : SL(6, ZMod 2)} (hj : j ∈ Jgrp)
    (h : ∀ w ∈ Wsp, cubeAct j w = w) {i a : Fin 4} (hia : i ≠ a) : ym j i a = 0 := by
  obtain ⟨k, hki, hka⟩ := exists_ne_two i a hia
  have hE1 := minor_eq_all hj h i k i k
  have hE2 := minor_eq_all hj h i k i a
  have hE3 := minor_eq_all hj h i k a k
  have hik : i ≠ k := fun hh => hki hh.symm
  simp [if_neg hki, if_neg hik, if_neg hka, if_neg hia] at hE1 hE2 hE3
  have hcomb : ym j i k * (ym j i i * ym j k a - ym j i a * ym j k i) +
      ym j i i * (ym j i a * ym j k k - ym j i k * ym j k a) = ym j i a := by
    rw [show ym j i k * (ym j i i * ym j k a - ym j i a * ym j k i) +
        ym j i i * (ym j i a * ym j k k - ym j i k * ym j k a) =
        ym j i a * (ym j i i * ym j k k - ym j i k * ym j k i) from by ring,
      show ym j i i * ym j k k - ym j i k * ym j k i = 1 from hE1, mul_one]
  rw [hE2, hE3] at hcomb
  simp at hcomb
  exact hcomb.symm

private theorem ym_diag {j : SL(6, ZMod 2)} (hj : j ∈ Jgrp)
    (h : ∀ w ∈ Wsp, cubeAct j w = w) (i : Fin 4) : ym j i i = 1 := by
  obtain ⟨k, hk⟩ := exists_ne i
  have hE1 := minor_eq_all hj h i k i k
  have hik : i ≠ k := fun hh => hk hh.symm
  have hoff1 : ym j i k = 0 := ym_offdiag hj h hik
  have hoff2 : ym j k i = 0 := ym_offdiag hj h hk
  simp [if_neg hk, if_neg hik, hoff1, hoff2] at hE1
  exact hE1.1

private theorem ym_eq_delta {j : SL(6, ZMod 2)} (hj : j ∈ Jgrp)
    (h : ∀ w ∈ Wsp, cubeAct j w = w) (i a : Fin 4) :
    ym j i a = if i = a then 1 else 0 := by
  by_cases hia : i = a
  · subst hia; simpa using ym_diag hj h i
  · rw [ym_offdiag hj h hia]; simp [if_neg hia]

private theorem jj_eq_one {j : SL(6, ZMod 2)} (hj : j ∈ Jgrp)
    (h : ∀ w ∈ Wsp, cubeAct j w = w) : j = 1 := by
  have hmid : ∀ i : Fin 4, (j : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
      (A5Cube.e (ZMod 2) (mid i)) = A5Cube.e (ZMod 2) (mid i) := by
    intro i
    have hmem := ym_mem_M0 hj i
    funext c
    obtain ⟨h0, h5⟩ := mem_M0_iff.mp hmem
    by_cases hc0 : c = 0
    · subst hc0; exact h0
    by_cases hc5 : c = 5
    · subst hc5; simpa [A5Cube.e, Pi.single_apply, mid_ne_five i] using h5
    obtain ⟨i', rfl⟩ : ∃ i' : Fin 4, mid i' = c := by
      fin_cases c <;> (first | decide | (exfalso; simp_all))
    have hd := ym_eq_delta hj h i i'
    simpa [ym, cv, A5Cube.e, Pi.single_apply, mid_eq_iff, eq_comm] using hd
  have hbasis : ∀ c : Fin 6, (j : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
      (A5Cube.e (ZMod 2) c) = A5Cube.e (ZMod 2) c := by
    intro c
    by_cases hc0 : c = 0
    · subst hc0; exact jj_fix_zero hj
    by_cases hc5 : c = 5
    · subst hc5; exact Jgrp_le_FixVec_five hj
    obtain ⟨i, rfl⟩ : ∃ i : Fin 4, mid i = c := by
      fin_cases c <;> (first | decide | (exfalso; simp_all))
    exact hmid i
  have hspan : Submodule.span (ZMod 2) (Set.range (A5Cube.e (ZMod 2))) = ⊤ := by
    rw [show A5Cube.e (ZMod 2) = ⇑(Pi.basisFun (ZMod 2) (Fin 6)) from by
      funext i; exact (Pi.basisFun_apply (ZMod 2) (Fin 6) i).symm]
    exact (Pi.basisFun (ZMod 2) (Fin 6)).span_eq
  have hvec : ∀ x : Fin 6 → ZMod 2, (j : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec x = x := by
    intro x
    have hx : x ∈ Submodule.span (ZMod 2) (Set.range (A5Cube.e (ZMod 2))) := by
      rw [hspan]; exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun y _ => (j : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec y = y) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨c, rfl⟩; exact hbasis c
    · simp
    · intro a b _ _ ha hb; rw [Matrix.mulVec_add, ha, hb]
    · intro r a _ ha; rw [Matrix.mulVec_smul, ha]
  have hmat : (j : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    ext r c
    have h2 := congrFun (hvec (Pi.single c 1)) r
    rw [Matrix.mulVec_single_one] at h2
    simpa [Matrix.col, Pi.single_apply, Matrix.one_apply] using h2
  exact Subtype.ext hmat

theorem cubeAct_apply_eq_of_mem_Sgrp {g : SL(6, ZMod 2)} (hg : g ∈ Sgrp)
    {w : A5Cube.Cube (ZMod 2)} (hw : w ∈ Wsp) : cubeAct g w = w :=
  Sgrp_le_Ksub hg w hw

theorem mem_Sgrp_of_cubeAct_eq_on_Wsp {g : SL(6, ZMod 2)} (hg : g ∈ Sgrp ⊔ Jgrp)
    (h : ∀ w ∈ Wsp, cubeAct g w = w) : g ∈ Sgrp := by
  obtain ⟨s, hs, j, hj, hgs⟩ := (mem_Sgrp_sup_Jgrp_iff g).mp hg
  have hj_eq : j = s⁻¹ * g := by rw [hgs]; group
  have hfixj : ∀ w ∈ Wsp, cubeAct j w = w := by
    intro w hw
    rw [hj_eq, cubeAct_mul]
    change cubeAct s⁻¹ (cubeAct g w) = w
    rw [h w hw]
    exact cubeAct_apply_eq_of_mem_Sgrp (Sgrp.inv_mem hs) hw
  have hgj : j = 1 := jj_eq_one hj hfixj
  rw [hgs, hgj, mul_one]
  exact hs

end CFSG.StandardType.FF81.CentE6
