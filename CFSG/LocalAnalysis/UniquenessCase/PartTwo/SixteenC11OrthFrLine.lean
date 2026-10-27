module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open scoped Matrix

abbrev S16C11FrIdx (m : ℕ) : Type := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2

abbrev S16C11FrVec (m : ℕ) : Type := S16C11FrIdx m → ZMod 2

abbrev S16C11FrQ (m : ℕ) : S16C11FrVec m → ZMod 2 := StatedQuadMinus m (ZMod 2) 1 1

abbrev S16C11FrO (m : ℕ) : Subgroup (Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :=
  CFSG.MatrixModel.isometryCore (S16C11FrQ m)

@[expose] def s16c11FrX (m i : ℕ) : S16C11FrIdx m :=
  if h : i < m - 1 then Sum.inl ⟨i, h⟩ else Sum.inr (Sum.inr 0)

@[expose] def s16c11FrE (m i : ℕ) : S16C11FrVec m := Pi.single (s16c11FrX m i) 1

@[expose] def s16c11FrLine (m : ℕ) : Finset (S16C11FrVec m) :=
  {s16c11FrE m 0, s16c11FrE m 1, s16c11FrE m 0 + s16c11FrE m 1}

@[expose] def s16c11FrP (m : ℕ) : Subgroup ↥(S16C11FrO m) where
  carrier := {g | (∀ w ∈ s16c11FrLine m,
      ((g : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w ∈ s16c11FrLine m) ∧
    (∀ w ∈ s16c11FrLine m,
      (((g⁻¹ : ↥(S16C11FrO m)) : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w ∈ s16c11FrLine m)}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · have h := ha1 _ (hb1 w hw)
      simpa [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec] using h
    · have h := hb2 _ (ha2 w hw)
      simpa [mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec] using h
  one_mem' := by
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩ <;> simpa using hw
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨ha2, by simpa [inv_inv] using ha1⟩

@[expose] def s16c11FrK (m : ℕ) : Subgroup ↥(S16C11FrO m) where
  carrier := {g | ∀ w ∈ s16c11FrLine m,
      ((g : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w = w}
  mul_mem' := by
    intro a b ha hb w hw
    have h := ha w hw
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb w hw]
    exact h
  one_mem' := by
    intro w hw
    simp
  inv_mem' := by
    intro a ha w hw
    have h := ha w hw
    have h2 : (((a⁻¹ : ↥(S16C11FrO m)) : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ
        ((((a : ↥(S16C11FrO m)) : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
          Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
        Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
    rw [h] at h2
    exact h2

private def s16c11_frY (m i : ℕ) : S16C11FrIdx m :=
  if h : i < m - 1 then Sum.inr (Sum.inl ⟨i, h⟩) else Sum.inr (Sum.inr 0)

private def s16c11_frSwapA (m : ℕ) : S16C11FrIdx m → S16C11FrIdx m := fun c =>
  if c = s16c11FrX m 0 then s16c11FrX m 1
  else if c = s16c11FrX m 1 then s16c11FrX m 0
  else if c = s16c11_frY m 0 then s16c11_frY m 1
  else if c = s16c11_frY m 1 then s16c11_frY m 0
  else c

private def s16c11_frMatA (m : ℕ) : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2) :=
  Matrix.of fun r c => if s16c11_frSwapA m c = r then 1 else 0

private def s16c11_frMatB (m : ℕ) : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2) :=
  1 + Matrix.single (s16c11FrX m 0) (s16c11FrX m 1) 1 +
    Matrix.single (s16c11_frY m 1) (s16c11_frY m 0) 1

private lemma s16c11_frMatA_mul_self {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11_frMatA m * s16c11_frMatA m = 1 := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_frMatB_mul_self {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11_frMatB m * s16c11_frMatB m = 1 := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_frMatA_isom {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∀ v : S16C11FrVec m,
      S16C11FrQ m (Matrix.mulVec (s16c11_frMatA m) v) = S16C11FrQ m v := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_frMatB_isom {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∀ v : S16C11FrVec m,
      S16C11FrQ m (Matrix.mulVec (s16c11_frMatB m) v) = S16C11FrQ m v := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_frMatA_maps_line {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∀ w ∈ s16c11FrLine m, Matrix.mulVec (s16c11_frMatA m) w ∈ s16c11FrLine m := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_frMatB_maps_line {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∀ w ∈ s16c11FrLine m, Matrix.mulVec (s16c11_frMatB m) w ∈ s16c11FrLine m := by
  rcases hm with rfl | rfl <;> decide +kernel

private def s16c11_frGenA (m : ℕ) (hm : m = 3 ∨ m = 4) :
    Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2) :=
  ⟨s16c11_frMatA m, s16c11_frMatA m, s16c11_frMatA_mul_self hm, s16c11_frMatA_mul_self hm⟩

private def s16c11_frGenB (m : ℕ) (hm : m = 3 ∨ m = 4) :
    Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2) :=
  ⟨s16c11_frMatB m, s16c11_frMatB m, s16c11_frMatB_mul_self hm, s16c11_frMatB_mul_self hm⟩

private lemma s16c11_frGenA_mem_O {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11_frGenA m hm ∈ S16C11FrO m := by
  refine Subgroup.subset_closure ?_
  intro v
  change S16C11FrQ m (Matrix.mulVec (s16c11_frMatA m) v) = S16C11FrQ m v
  exact s16c11_frMatA_isom hm v

private lemma s16c11_frGenB_mem_O {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11_frGenB m hm ∈ S16C11FrO m := by
  refine Subgroup.subset_closure ?_
  intro v
  change S16C11FrQ m (Matrix.mulVec (s16c11_frMatB m) v) = S16C11FrQ m v
  exact s16c11_frMatB_isom hm v

private def s16c11_frGA (m : ℕ) (hm : m = 3 ∨ m = 4) : ↥(S16C11FrO m) :=
  ⟨s16c11_frGenA m hm, s16c11_frGenA_mem_O hm⟩

private def s16c11_frGB (m : ℕ) (hm : m = 3 ∨ m = 4) : ↥(S16C11FrO m) :=
  ⟨s16c11_frGenB m hm, s16c11_frGenB_mem_O hm⟩

private lemma s16c11_frGA_mem_P {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11_frGA m hm ∈ s16c11FrP m := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · change Matrix.mulVec (s16c11_frMatA m) w ∈ s16c11FrLine m
    exact s16c11_frMatA_maps_line hm w hw
  · change Matrix.mulVec (s16c11_frMatA m) w ∈ s16c11FrLine m
    exact s16c11_frMatA_maps_line hm w hw

private lemma s16c11_frGB_mem_P {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11_frGB m hm ∈ s16c11FrP m := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · change Matrix.mulVec (s16c11_frMatB m) w ∈ s16c11FrLine m
    exact s16c11_frMatB_maps_line hm w hw
  · change Matrix.mulVec (s16c11_frMatB m) w ∈ s16c11FrLine m
    exact s16c11_frMatB_maps_line hm w hw

private def s16c11_frPa (m : ℕ) (hm : m = 3 ∨ m = 4) : ↥(s16c11FrP m) :=
  ⟨s16c11_frGA m hm, s16c11_frGA_mem_P hm⟩

private def s16c11_frPb (m : ℕ) (hm : m = 3 ∨ m = 4) : ↥(s16c11FrP m) :=
  ⟨s16c11_frGB m hm, s16c11_frGB_mem_P hm⟩

@[simp] private lemma s16c11_frPa_coe (m : ℕ) (hm : m = 3 ∨ m = 4) :
    ((((s16c11_frPa m hm : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) = s16c11_frMatA m := rfl

@[simp] private lemma s16c11_frPb_coe (m : ℕ) (hm : m = 3 ∨ m = 4) :
    ((((s16c11_frPb m hm : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) = s16c11_frMatB m := rfl

private lemma s16c11_frP_coe_mul {m : ℕ} (a b : ↥(s16c11FrP m)) :
    ((((a * b : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) = ((((a : ↥(s16c11FrP m)) : ↥(S16C11FrO m))
          :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) * ((((b : ↥(s16c11FrP m)) : ↥(S16C11FrO m))
          :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul]

private lemma s16c11_frMatA_e0 {m : ℕ} (hm : m = 3 ∨ m = 4) :
    Matrix.mulVec (s16c11_frMatA m) (s16c11FrE m 0) = s16c11FrE m 1 := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_frMatA_e1 {m : ℕ} (hm : m = 3 ∨ m = 4) :
    Matrix.mulVec (s16c11_frMatA m) (s16c11FrE m 1) = s16c11FrE m 0 := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_frMatB_e0 {m : ℕ} (hm : m = 3 ∨ m = 4) :
    Matrix.mulVec (s16c11_frMatB m) (s16c11FrE m 0) = s16c11FrE m 0 := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_frMatB_e1 {m : ℕ} (hm : m = 3 ∨ m = 4) :
    Matrix.mulVec (s16c11_frMatB m) (s16c11FrE m 1) =
      s16c11FrE m 0 + s16c11FrE m 1 := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_frMatB_e01 {m : ℕ} (hm : m = 3 ∨ m = 4) :
    Matrix.mulVec (s16c11_frMatB m) (s16c11FrE m 0 + s16c11FrE m 1) =
      s16c11FrE m 1 := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_frE0_ne_E1 {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11FrE m 0 ≠ s16c11FrE m 1 := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_frE1_ne_E01 {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11FrE m 1 ≠ s16c11FrE m 0 + s16c11FrE m 1 := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_fr_line_card {m : ℕ} (hm : m = 3 ∨ m = 4) :
    (s16c11FrLine m).card = 3 := by
  rcases hm with rfl | rfl <;> decide +kernel

private lemma s16c11_fr_mem_line {m : ℕ} {w : S16C11FrVec m} :
    w ∈ s16c11FrLine m ↔
      w = s16c11FrE m 0 ∨ w = s16c11FrE m 1 ∨ w = s16c11FrE m 0 + s16c11FrE m 1 := by
  simp [s16c11FrLine]

theorem s16c11_fr_K_le_P (m : ℕ) : s16c11FrK m ≤ s16c11FrP m := by
  intro g hg
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rw [hg w hw]
    exact hw
  · have h2 : (((g⁻¹ : ↥(S16C11FrO m)) :
      Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
      Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ ((((g : ↥(S16C11FrO m)) :
      Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
      Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
        Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
    rw [hg w hw] at h2
    rw [h2]
    exact hw

theorem s16c11_fr_K_normal (m : ℕ) :
    ((s16c11FrK m).subgroupOf (s16c11FrP m)).Normal := by
  refine ⟨fun n hn p => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  intro w hw
  have hp2 : ((((p⁻¹ : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w ∈ s16c11FrLine m := p.2.2 w hw
  have hn' : ((((n : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ (((((p⁻¹ : ↥(s16c11FrP m)) : ↥(S16C11FrO
          m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w) = ((((p⁻¹ : ↥(s16c11FrP m)) :
          ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w :=
    hn _ hp2
  have hp1 : ((((p : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ (((((p⁻¹ : ↥(s16c11FrP m)) : ↥(S16C11FrO
          m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← s16c11_frP_coe_mul p p⁻¹, mul_inv_cancel]
    simp
  rw [s16c11_frP_coe_mul (p * n) p⁻¹, s16c11_frP_coe_mul p n]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hn', hp1]

theorem s16c11_fr_K_index {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ((s16c11FrK m).subgroupOf (s16c11FrP m)).index = 6 := by
  classical
  let V := S16C11FrVec m
  letI : MulAction ↥(s16c11FrP m) V :=
    { smul := fun g w => ((((g : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w
      one_smul := by
        intro w
        show (((((1 : ↥(s16c11FrP m)) : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w = w
        simp
      mul_smul := by
        intro g h w
        show ((((g * h : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w = ((((g : ↥(s16c11FrP m)) :
          ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ (((((h : ↥(s16c11FrP m)) : ↥(S16C11FrO
          m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w)
        rw [s16c11_frP_coe_mul g h, Matrix.mulVec_mulVec] }
  let Stab := MulAction.stabilizer ↥(s16c11FrP m) (s16c11FrE m 0)
  let H := (s16c11FrK m).subgroupOf (s16c11FrP m)
  have hHle : H ≤ Stab := by
    intro k hk
    change k ∈ MulAction.stabilizer ↥(s16c11FrP m) (s16c11FrE m 0)
    rw [MulAction.mem_stabilizer_iff]
    rw [Subgroup.mem_subgroupOf] at hk
    exact hk (s16c11FrE m 0) (by simp [s16c11FrLine])
  have horbit : MulAction.orbit ↥(s16c11FrP m) (s16c11FrE m 0) =
      (s16c11FrLine m : Set V) := by
    apply Set.Subset.antisymm
    · rintro v ⟨g, rfl⟩
      exact g.2.1 (s16c11FrE m 0) (by simp [s16c11FrLine])
    · intro w hw
      rw [Finset.mem_coe, s16c11_fr_mem_line] at hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨1, one_smul _ _⟩
      · refine ⟨s16c11_frPa m hm, ?_⟩
        show ((((s16c11_frPa m hm : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ s16c11FrE m 0 = s16c11FrE m 1
        rw [s16c11_frPa_coe]
        exact s16c11_frMatA_e0 hm
      · refine ⟨s16c11_frPb m hm * s16c11_frPa m hm, ?_⟩
        show ((((s16c11_frPb m hm * s16c11_frPa m hm : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ s16c11FrE m 0 =
          s16c11FrE m 0 + s16c11FrE m 1
        rw [s16c11_frP_coe_mul (s16c11_frPb m hm) (s16c11_frPa m hm),
          ← Matrix.mulVec_mulVec, s16c11_frPa_coe, s16c11_frMatA_e0 hm,
          s16c11_frPb_coe, s16c11_frMatB_e1 hm]
  have hidx1 : Stab.index = 3 := by
    change (MulAction.stabilizer ↥(s16c11FrP m) (s16c11FrE m 0)).index = 3
    have h := MulAction.index_stabilizer (G := ↥(s16c11FrP m)) (x := s16c11FrE m 0)
    rw [horbit] at h
    rw [h, Set.ncard_coe_finset, s16c11_fr_line_card hm]
  have hstab2 : MulAction.stabilizer ↥Stab (s16c11FrE m 1) = H.subgroupOf Stab := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      have hk0 : (((((k : ↥(s16c11FrP m)) : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ s16c11FrE m 0 = s16c11FrE m 0 := by
        have h := k.2
        change k.1 ∈ MulAction.stabilizer ↥(s16c11FrP m) (s16c11FrE m 0) at h
        rw [MulAction.mem_stabilizer_iff] at h
        exact h
      have hk1 : (((((k : ↥(s16c11FrP m)) : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ s16c11FrE m 1 = s16c11FrE m 1 := hk
      intro w hw
      rw [s16c11_fr_mem_line] at hw
      rcases hw with rfl | rfl | rfl
      · exact hk0
      · exact hk1
      · rw [Matrix.mulVec_add, hk0, hk1]
    · intro hk
      exact hk (s16c11FrE m 1) (by simp [s16c11FrLine])
  have horbit2 : MulAction.orbit ↥Stab (s16c11FrE m 1) =
      ({s16c11FrE m 1, s16c11FrE m 0 + s16c11FrE m 1} : Set V) := by
    apply Set.Subset.antisymm
    · rintro v ⟨k, rfl⟩
      have hlin : (((((k : ↥(s16c11FrP m)) : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ s16c11FrE m 1 ∈
          s16c11FrLine m :=
        (k : ↥(s16c11FrP m)).2.1 (s16c11FrE m 1) (by simp [s16c11FrLine])
      have hne : (((((k : ↥(s16c11FrP m)) : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ s16c11FrE m 1 ≠ s16c11FrE m 0 := by
        intro hcontra
        have hk0' : (k⁻¹ : ↥Stab) • (s16c11FrE m 0) = s16c11FrE m 0 := by
          have h := (k⁻¹ : ↥Stab).2
          change (k⁻¹ : ↥Stab).1 ∈
            MulAction.stabilizer ↥(s16c11FrP m) (s16c11FrE m 0) at h
          rw [MulAction.mem_stabilizer_iff] at h
          exact h
        have h1 : (k⁻¹ : ↥Stab) • (s16c11FrE m 0) = s16c11FrE m 1 := by
          have h2 : (k : ↥Stab) • (s16c11FrE m 1) = s16c11FrE m 0 := hcontra
          calc (k⁻¹ : ↥Stab) • (s16c11FrE m 0)
              = (k⁻¹ : ↥Stab) • ((k : ↥Stab) • (s16c11FrE m 1)) := by rw [h2]
            _ = s16c11FrE m 1 := by rw [← mul_smul, inv_mul_cancel, one_smul]
        exact (s16c11_frE0_ne_E1 hm) (by rw [← hk0', h1])
      show (((((k : ↥(s16c11FrP m)) : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ s16c11FrE m 1 ∈
        ({s16c11FrE m 1, s16c11FrE m 0 + s16c11FrE m 1} : Set V)
      rw [s16c11_fr_mem_line] at hlin
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hlin with h | h | h
      · exact absurd h hne
      · exact Or.inl h
      · exact Or.inr h
    · intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact ⟨1, one_smul _ _⟩
      · refine ⟨⟨s16c11_frPb m hm, ?_⟩, ?_⟩
        · change s16c11_frPb m hm ∈
            MulAction.stabilizer ↥(s16c11FrP m) (s16c11FrE m 0)
          rw [MulAction.mem_stabilizer_iff]
          show ((((s16c11_frPb m hm : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ s16c11FrE m 0 = s16c11FrE m 0
          rw [s16c11_frPb_coe]
          exact s16c11_frMatB_e0 hm
        · show ((((s16c11_frPb m hm : ↥(s16c11FrP m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ s16c11FrE m 1 =
            s16c11FrE m 0 + s16c11FrE m 1
          rw [s16c11_frPb_coe]
          exact s16c11_frMatB_e1 hm
  have hidx2 : H.relIndex Stab = 2 := by
    change (H.subgroupOf Stab).index = 2
    have h := MulAction.index_stabilizer (G := ↥Stab) (x := s16c11FrE m 1)
    rw [hstab2, horbit2] at h
    rw [h, Set.ncard_pair (s16c11_frE1_ne_E01 hm)]
  change H.index = 6
  rw [← Subgroup.relIndex_mul_index hHle, hidx2, hidx1]

theorem s16c11_fr_P_moves {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∀ y ∈ s16c11FrLine m, ∃ p ∈ s16c11FrP m,
      ((p : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ y ≠ y := by
  intro y hy
  rw [s16c11_fr_mem_line] at hy
  rcases hy with rfl | rfl | rfl
  · refine ⟨s16c11_frGA m hm, s16c11_frGA_mem_P hm, ?_⟩
    change Matrix.mulVec (s16c11_frMatA m) (s16c11FrE m 0) ≠ s16c11FrE m 0
    rw [s16c11_frMatA_e0 hm]
    exact fun h => s16c11_frE0_ne_E1 hm h.symm
  · refine ⟨s16c11_frGA m hm, s16c11_frGA_mem_P hm, ?_⟩
    change Matrix.mulVec (s16c11_frMatA m) (s16c11FrE m 1) ≠ s16c11FrE m 1
    rw [s16c11_frMatA_e1 hm]
    exact s16c11_frE0_ne_E1 hm
  · refine ⟨s16c11_frGB m hm, s16c11_frGB_mem_P hm, ?_⟩
    change Matrix.mulVec (s16c11_frMatB m) (s16c11FrE m 0 + s16c11FrE m 1) ≠
      s16c11FrE m 0 + s16c11FrE m 1
    rw [s16c11_frMatB_e01 hm]
    exact s16c11_frE1_ne_E01 hm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
