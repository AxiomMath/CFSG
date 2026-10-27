module

public import CFSG.Quasithin.Background.FLcModel
public import CFSG.Quasithin.Background.CubicCount
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic

public section

namespace CFSG.Quasithin.SevenL4Model

open Matrix CFSG.Quasithin.CubicCount CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L (blkAt blkAt_apply)

@[expose] def x1M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 0]

@[expose] def x3M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

@[expose] def k0M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0]

theorem det_x1M : x1M.det = 1 := by decide +kernel

theorem det_x3M : x3M.det = 1 := by decide +kernel

theorem det_k0M : k0M.det = 1 := by decide +kernel

@[expose] def x1 : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨x1M, det_x1M⟩

@[expose] def x3 : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨x3M, det_x3M⟩

@[expose] def k0 : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨k0M, det_k0M⟩

theorem x1_pow_seven : x1 ^ 7 = 1 := by decide +kernel

theorem x3_pow_seven : x3 ^ 7 = 1 := by decide +kernel

theorem x1_ne_one : x1 ≠ 1 := by decide +kernel

theorem x3_ne_one : x3 ≠ 1 := by decide +kernel

theorem k0_mul_x1 : k0 * x1 = x3 * k0 := by decide +kernel

theorem k0_conj_x1 : k0 * x1 * k0⁻¹ = x3 := by
  rw [k0_mul_x1, mul_inv_cancel_right]

theorem x1_eq_prod :
    x1 = SpecialLinearGroup.transvection (i := (1 : Fin 4)) (j := 2) (by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (i := (2 : Fin 4)) (j := 1) (by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (i := (2 : Fin 4)) (j := 3) (by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (i := (3 : Fin 4)) (j := 2) (by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (i := (2 : Fin 4)) (j := 3) (by decide) (1 : ZMod 2) := by
  decide +kernel

theorem x3_eq_prod :
    x3 = SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := 1) (by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (i := (1 : Fin 4)) (j := 0) (by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (i := (1 : Fin 4)) (j := 2) (by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (i := (2 : Fin 4)) (j := 1) (by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (i := (1 : Fin 4)) (j := 2) (by decide) (1 : ZMod 2) := by
  decide +kernel

@[expose] def rad1M (c : Fin 3 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, c 0, c 1, c 2; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def rad3M (c : Fin 3 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, c 0; 0, 1, 0, c 1; 0, 0, 1, c 2; 0, 0, 0, 1]

theorem rad1M_mul : ∀ c c', rad1M c * rad1M c' = rad1M (c + c') := by decide +kernel

theorem rad3M_mul : ∀ c c', rad3M c * rad3M c' = rad3M (c + c') := by decide +kernel

theorem rad1M_zero : rad1M 0 = 1 := by decide +kernel

theorem rad3M_zero : rad3M 0 = 1 := by decide +kernel

theorem rad1M_mul_self : ∀ c, rad1M c * rad1M c = 1 := by decide +kernel

theorem rad3M_mul_self : ∀ c, rad3M c * rad3M c = 1 := by decide +kernel

theorem det_rad1M : ∀ c, (rad1M c).det = 1 := by decide +kernel

theorem det_rad3M : ∀ c, (rad3M c).det = 1 := by decide +kernel

@[expose] def rad1Fun (c : Fin 3 → ZMod 2) : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨rad1M c, det_rad1M c⟩

@[expose] def rad3Fun (c : Fin 3 → ZMod 2) : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨rad3M c, det_rad3M c⟩

@[expose] def rad1 : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) where
  carrier := Set.range rad1Fun
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    exact ⟨c + c', Subtype.ext (rad1M_mul c c').symm⟩
  one_mem' := ⟨0, Subtype.ext rad1M_zero⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    have h : rad1Fun c * rad1Fun c = 1 := Subtype.ext (rad1M_mul_self c)
    exact ⟨c, (inv_eq_of_mul_eq_one_right h).symm⟩

@[expose] def rad3 : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) where
  carrier := Set.range rad3Fun
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    exact ⟨c + c', Subtype.ext (rad3M_mul c c').symm⟩
  one_mem' := ⟨0, Subtype.ext rad3M_zero⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    have h : rad3Fun c * rad3Fun c = 1 := Subtype.ext (rad3M_mul_self c)
    exact ⟨c, (inv_eq_of_mul_eq_one_right h).symm⟩

theorem mem_rad1 {g : SpecialLinearGroup (Fin 4) (ZMod 2)} :
    g ∈ rad1 ↔ ∃ c, g.1 = rad1M c :=
  ⟨fun ⟨c, hc⟩ => ⟨c, by rw [← hc]; rfl⟩, fun ⟨c, hc⟩ => ⟨c, Subtype.ext hc.symm⟩⟩

theorem mem_rad3 {g : SpecialLinearGroup (Fin 4) (ZMod 2)} :
    g ∈ rad3 ↔ ∃ c, g.1 = rad3M c :=
  ⟨fun ⟨c, hc⟩ => ⟨c, by rw [← hc]; rfl⟩, fun ⟨c, hc⟩ => ⟨c, Subtype.ext hc.symm⟩⟩

theorem cubAct_x1_rad1M : ∀ c : Fin 3 → ZMod 2,
    x1M ^ 3 * rad1M c * x1M ^ 4 * (x1M ^ 2 * rad1M c * x1M ^ 5) * rad1M c = 1 := by
  decide +kernel

theorem cubAct_x3_rad3M : ∀ c : Fin 3 → ZMod 2,
    x3M ^ 3 * rad3M c * x3M ^ 4 * (x3M ^ 1 * rad3M c * x3M ^ 6) * rad3M c = 1 := by
  decide +kernel

theorem cubAct_x1_rad1 : ∀ r ∈ rad1, cubAct true x1 r = 1 := by
  rintro _ ⟨c, rfl⟩
  have h4 : (x1 ^ 3)⁻¹ = x1 ^ 4 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_add, x1_pow_seven])
  have h5 : (x1 ^ 2)⁻¹ = x1 ^ 5 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_add, x1_pow_seven])
  show x1 ^ 3 * rad1Fun c * (x1 ^ 3)⁻¹ * (x1 ^ 2 * rad1Fun c * (x1 ^ 2)⁻¹) * rad1Fun c = 1
  rw [h4, h5]
  exact Subtype.ext (cubAct_x1_rad1M c)

theorem cubAct_x3_rad3 : ∀ r ∈ rad3, cubAct false x3 r = 1 := by
  rintro _ ⟨c, rfl⟩
  have h4 : (x3 ^ 3)⁻¹ = x3 ^ 4 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_add, x3_pow_seven])
  have h6 : (x3 ^ 1)⁻¹ = x3 ^ 6 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_add, x3_pow_seven])
  show x3 ^ 3 * rad3Fun c * (x3 ^ 3)⁻¹ * (x3 ^ 1 * rad3Fun c * (x3 ^ 1)⁻¹) * rad3Fun c = 1
  rw [h4, h6]
  exact Subtype.ext (cubAct_x3_rad3M c)

theorem mem_rad1_of_blk {g : SpecialLinearGroup (Fin 4) (ZMod 2)} (hg : g ∈ FLc.QI 4 {1})
    (hb : blkAt 1 3 (by norm_num) g.1 = 1) : g ∈ rad1 := by
  have hst : g ∈ stabilizer (flagSpace 4 (ZMod 2) 1) := (mem_flagStabilizer.mp hg) 1 rfl
  rw [CFSG.LieType.SteinbergBR.BlockPar.mem_stabilizer_flagSpace_iff] at hst
  have hb' : ∀ a b : Fin 3, g.1 a.succ b.succ = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) a b := by
    intro a b
    have := congrFun₂ hb a b
    rw [blkAt_apply] at this
    convert this using 2 <;> exact Fin.ext (by simp [Fin.val_succ, add_comm])
  have hcol : ∀ a : Fin 3, g.1 a.succ 0 = 0 := fun a =>
    hst a.succ 0 (by simp [Fin.val_succ]) (by simp)
  have h00 : g.1 0 0 = 1 := by
    by_contra h0
    have hz : g.1 0 0 = 0 := by
      generalize g.1 0 0 = x at h0
      revert x
      decide
    have hdet : g.1.det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero 0
      intro i
      refine Fin.cases ?_ (fun a => ?_) i
      · exact hz
      · exact hcol a
    rw [g.2] at hdet
    exact one_ne_zero hdet
  refine mem_rad1.mpr ⟨fun k => g.1 0 k.succ, ?_⟩
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · rw [h00]
    rfl
  · fin_cases b <;> rfl
  · rw [hcol a]
    fin_cases a <;> rfl
  · rw [hb' a b]
    fin_cases a <;> fin_cases b <;> rfl

theorem mem_rad3_of_blk {g : SpecialLinearGroup (Fin 4) (ZMod 2)} (hg : g ∈ FLc.QI 4 {3})
    (hb : blkAt 0 3 (by norm_num) g.1 = 1) : g ∈ rad3 := by
  have hst : g ∈ stabilizer (flagSpace 4 (ZMod 2) 3) := (mem_flagStabilizer.mp hg) 3 rfl
  rw [CFSG.LieType.SteinbergBR.BlockPar.mem_stabilizer_flagSpace_iff] at hst
  have hb' : ∀ a b : Fin 3, g.1 a.castSucc b.castSucc =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) a b := by
    intro a b
    have := congrFun₂ hb a b
    rw [blkAt_apply] at this
    convert this using 2 <;> exact Fin.ext (by simp)
  have hrow : ∀ a : Fin 3, g.1 (Fin.last 3) a.castSucc = 0 := fun a =>
    hst (Fin.last 3) a.castSucc (by simp) (by simp)
  have h33 : g.1 (Fin.last 3) (Fin.last 3) = 1 := by
    by_contra h0
    have hz : g.1 (Fin.last 3) (Fin.last 3) = 0 := by
      generalize g.1 (Fin.last 3) (Fin.last 3) = x at h0
      revert x
      decide
    have hdet : g.1.det = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last 3)
      intro j
      refine Fin.lastCases ?_ (fun a => ?_) j
      · exact hz
      · exact hrow a
    rw [g.2] at hdet
    exact one_ne_zero hdet
  refine mem_rad3.mpr ⟨fun k => g.1 k.castSucc (Fin.last 3), ?_⟩
  ext i j
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · rw [h33]
    rfl
  · rw [hrow b]
    fin_cases b <;> rfl
  · fin_cases a <;> rfl
  · rw [hb' a b]
    fin_cases a <;> fin_cases b <;> rfl

theorem sl3_seven : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M ^ 7 = 1 → M ≠ 1 →
    (M ^ 3 + M + 1 = 0 ∧ (M ^ 6).transpose ^ 3 + (M ^ 6).transpose ^ 2 + 1 = 0) ∨
      (M ^ 3 + M ^ 2 + 1 = 0 ∧ (M ^ 6).transpose ^ 3 + (M ^ 6).transpose + 1 = 0) := by
  decide +kernel

end CFSG.Quasithin.SevenL4Model
