module

public import CFSG.RankThree.PartOne.KF4.ShortA2Data
public import CFSG.RankThree.PartOne.KF4.SymSquare

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped Pointwise

section Mats

variable {K : Type} [Field K]

theorem f4Short_str : ∀ k : Fin 6, ∀ i : Fin Tag.F4.rank, (i = f4Index 2 ∨ i = f4Index 3) →
    stringUp Tag.F4 i (f4ShortWeight k) = f4StrUp i (f4ShortWeight k) ∧
      stringDown Tag.F4 i (f4ShortWeight k) = f4StrDown i (f4ShortWeight k) := by
  intro k i hi
  have hroot : IsRoot Tag.F4 (f4ShortWeight k) := f4Short_data.isRoot k
  have hne := f4Short_data.ne_single k i ((mem_f4ShortSupport i).2 hi)
  exact stringUp_down_F4 i hroot hne.1 hne.2

@[expose] def f4ShortX3 (t : K) : Matrix (Fin 6) (Fin 6) K :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, t, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 2*t, t^2;
     0, 0, 0, 0, 1, t;
     0, 0, 0, 0, 0, 1]

theorem f4Short_x3_up (b : Fin 6) :
    stringUp Tag.F4 (f4Index 2) (f4ShortWeight b) = (![0, 0, 1, 0, 1, 2] : Fin 6 → ℕ) b := by
  rw [(f4Short_str b _ (Or.inl rfl)).1]
  fin_cases b <;> decide +kernel

theorem f4Short_x3_down (b : Fin 6) :
    stringDown Tag.F4 (f4Index 2) (f4ShortWeight b) = (![0, 1, 0, 2, 1, 0] : Fin 6 → ℕ) b := by
  rw [(f4Short_str b _ (Or.inl rfl)).2]
  fin_cases b <;> decide +kernel

theorem f4Short_x3_cols (t : K) (b : Fin 6) :
    xOp Tag.F4 K (f4Index 2) t (f4Short_data.vec K b) =
      ∑ a, f4ShortX3 t a b • f4Short_data.vec K a := by
  match b with
  | 0 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 0 0 0
        (by rw [f4Short_x3_up]; rfl) (by rw [f4Short_x3_down]; rfl)
        ![0] (by decide +kernel)]
    simp [f4ShortX3, Fin.sum_univ_succ]
  | 1 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 1 0 1
        (by rw [f4Short_x3_up]; rfl) (by rw [f4Short_x3_down]; rfl)
        ![1] (by decide +kernel)]
    simp [f4ShortX3, Fin.sum_univ_succ]
  | 2 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 2 1 0
        (by rw [f4Short_x3_up]; rfl) (by rw [f4Short_x3_down]; rfl)
        ![2, 1] (by decide +kernel)]
    simp [f4ShortX3, Fin.sum_univ_succ]
    abel
  | 3 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 3 0 2
        (by rw [f4Short_x3_up]; rfl) (by rw [f4Short_x3_down]; rfl)
        ![3] (by decide +kernel)]
    simp [f4ShortX3, Fin.sum_univ_succ]
  | 4 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 4 1 1
        (by rw [f4Short_x3_up]; rfl) (by rw [f4Short_x3_down]; rfl)
        ![4, 3] (by decide +kernel)]
    simp [f4ShortX3, Fin.sum_univ_succ]
    abel
  | 5 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 5 2 0
        (by rw [f4Short_x3_up]; rfl) (by rw [f4Short_x3_down]; rfl)
        ![5, 4, 3] (by decide +kernel)]
    simp [f4ShortX3, Fin.sum_univ_succ]
    abel

theorem f4Short_Mat_x3 (t : K) :
    f4Short_data.Mat (xUnit Tag.F4 K (f4Index 2) t) = f4ShortX3 t :=
  f4Short_data.Mat_eq_of_col _ (fun b => by
    rw [coe_xUnit]
    exact f4Short_x3_cols t b)

@[expose] def f4ShortY3 (t : K) : Matrix (Fin 6) (Fin 6) K :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, t, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, t, 1, 0;
     0, 0, 0, t^2, 2*t, 1]

theorem f4Short_y3_up (b : Fin 6) :
    stringUp Tag.F4 (f4Index 2) (f4ShortWeight b) = (![0, 0, 1, 0, 1, 2] : Fin 6 → ℕ) b := by
  rw [(f4Short_str b _ (Or.inl rfl)).1]
  fin_cases b <;> decide +kernel

theorem f4Short_y3_down (b : Fin 6) :
    stringDown Tag.F4 (f4Index 2) (f4ShortWeight b) = (![0, 1, 0, 2, 1, 0] : Fin 6 → ℕ) b := by
  rw [(f4Short_str b _ (Or.inl rfl)).2]
  fin_cases b <;> decide +kernel

theorem f4Short_y3_cols (t : K) (b : Fin 6) :
    yOp Tag.F4 K (f4Index 2) t (f4Short_data.vec K b) =
      ∑ a, f4ShortY3 t a b • f4Short_data.vec K a := by
  match b with
  | 0 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 0 0 0
        (by rw [f4Short_y3_up]; rfl) (by rw [f4Short_y3_down]; rfl)
        ![0] (by decide +kernel)]
    simp [f4ShortY3, Fin.sum_univ_succ]
  | 1 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 1 0 1
        (by rw [f4Short_y3_up]; rfl) (by rw [f4Short_y3_down]; rfl)
        ![1, 2] (by decide +kernel)]
    simp [f4ShortY3, Fin.sum_univ_succ]
  | 2 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 2 1 0
        (by rw [f4Short_y3_up]; rfl) (by rw [f4Short_y3_down]; rfl)
        ![2] (by decide +kernel)]
    simp [f4ShortY3, Fin.sum_univ_succ]
  | 3 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 3 0 2
        (by rw [f4Short_y3_up]; rfl) (by rw [f4Short_y3_down]; rfl)
        ![3, 4, 5] (by decide +kernel)]
    simp [f4ShortY3, Fin.sum_univ_succ]
  | 4 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 4 1 1
        (by rw [f4Short_y3_up]; rfl) (by rw [f4Short_y3_down]; rfl)
        ![4, 5] (by decide +kernel)]
    simp [f4ShortY3, Fin.sum_univ_succ]
  | 5 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inl rfl)) t 5 2 0
        (by rw [f4Short_y3_up]; rfl) (by rw [f4Short_y3_down]; rfl)
        ![5] (by decide +kernel)]
    simp [f4ShortY3, Fin.sum_univ_succ]

theorem f4Short_Mat_y3 (t : K) :
    f4Short_data.Mat (yUnit Tag.F4 K (f4Index 2) t) = f4ShortY3 t :=
  f4Short_data.Mat_eq_of_col _ (fun b => by
    rw [coe_yUnit]
    exact f4Short_y3_cols t b)

@[expose] def f4ShortX4 (t : K) : Matrix (Fin 6) (Fin 6) K :=
  !![1, 2*t, 0, t^2, 0, 0;
     0, 1, 0, t, 0, 0;
     0, 0, 1, 0, t, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

theorem f4Short_x4_up (b : Fin 6) :
    stringUp Tag.F4 (f4Index 3) (f4ShortWeight b) = (![0, 1, 0, 2, 1, 0] : Fin 6 → ℕ) b := by
  rw [(f4Short_str b _ (Or.inr rfl)).1]
  fin_cases b <;> decide +kernel

theorem f4Short_x4_down (b : Fin 6) :
    stringDown Tag.F4 (f4Index 3) (f4ShortWeight b) = (![2, 1, 1, 0, 0, 0] : Fin 6 → ℕ) b := by
  rw [(f4Short_str b _ (Or.inr rfl)).2]
  fin_cases b <;> decide +kernel

theorem f4Short_x4_cols (t : K) (b : Fin 6) :
    xOp Tag.F4 K (f4Index 3) t (f4Short_data.vec K b) =
      ∑ a, f4ShortX4 t a b • f4Short_data.vec K a := by
  match b with
  | 0 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 0 0 2
        (by rw [f4Short_x4_up]; rfl) (by rw [f4Short_x4_down]; rfl)
        ![0] (by decide +kernel)]
    simp [f4ShortX4, Fin.sum_univ_succ]
  | 1 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 1 1 1
        (by rw [f4Short_x4_up]; rfl) (by rw [f4Short_x4_down]; rfl)
        ![1, 0] (by decide +kernel)]
    simp [f4ShortX4, Fin.sum_univ_succ]
    abel
  | 2 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 2 0 1
        (by rw [f4Short_x4_up]; rfl) (by rw [f4Short_x4_down]; rfl)
        ![2] (by decide +kernel)]
    simp [f4ShortX4, Fin.sum_univ_succ]
  | 3 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 3 2 0
        (by rw [f4Short_x4_up]; rfl) (by rw [f4Short_x4_down]; rfl)
        ![3, 1, 0] (by decide +kernel)]
    simp [f4ShortX4, Fin.sum_univ_succ]
    abel
  | 4 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 4 1 0
        (by rw [f4Short_x4_up]; rfl) (by rw [f4Short_x4_down]; rfl)
        ![4, 2] (by decide +kernel)]
    simp [f4ShortX4, Fin.sum_univ_succ]
    abel
  | 5 =>
    rw [f4Short_data.xOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 5 0 0
        (by rw [f4Short_x4_up]; rfl) (by rw [f4Short_x4_down]; rfl)
        ![5] (by decide +kernel)]
    simp [f4ShortX4, Fin.sum_univ_succ]

theorem f4Short_Mat_x4 (t : K) :
    f4Short_data.Mat (xUnit Tag.F4 K (f4Index 3) t) = f4ShortX4 t :=
  f4Short_data.Mat_eq_of_col _ (fun b => by
    rw [coe_xUnit]
    exact f4Short_x4_cols t b)

@[expose] def f4ShortY4 (t : K) : Matrix (Fin 6) (Fin 6) K :=
  !![1, 0, 0, 0, 0, 0;
     t, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     t^2, 2*t, 0, 1, 0, 0;
     0, 0, t, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

theorem f4Short_y4_up (b : Fin 6) :
    stringUp Tag.F4 (f4Index 3) (f4ShortWeight b) = (![0, 1, 0, 2, 1, 0] : Fin 6 → ℕ) b := by
  rw [(f4Short_str b _ (Or.inr rfl)).1]
  fin_cases b <;> decide +kernel

theorem f4Short_y4_down (b : Fin 6) :
    stringDown Tag.F4 (f4Index 3) (f4ShortWeight b) = (![2, 1, 1, 0, 0, 0] : Fin 6 → ℕ) b := by
  rw [(f4Short_str b _ (Or.inr rfl)).2]
  fin_cases b <;> decide +kernel

theorem f4Short_y4_cols (t : K) (b : Fin 6) :
    yOp Tag.F4 K (f4Index 3) t (f4Short_data.vec K b) =
      ∑ a, f4ShortY4 t a b • f4Short_data.vec K a := by
  match b with
  | 0 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 0 0 2
        (by rw [f4Short_y4_up]; rfl) (by rw [f4Short_y4_down]; rfl)
        ![0, 1, 3] (by decide +kernel)]
    simp [f4ShortY4, Fin.sum_univ_succ]
  | 1 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 1 1 1
        (by rw [f4Short_y4_up]; rfl) (by rw [f4Short_y4_down]; rfl)
        ![1, 3] (by decide +kernel)]
    simp [f4ShortY4, Fin.sum_univ_succ]
  | 2 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 2 0 1
        (by rw [f4Short_y4_up]; rfl) (by rw [f4Short_y4_down]; rfl)
        ![2, 4] (by decide +kernel)]
    simp [f4ShortY4, Fin.sum_univ_succ]
  | 3 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 3 2 0
        (by rw [f4Short_y4_up]; rfl) (by rw [f4Short_y4_down]; rfl)
        ![3] (by decide +kernel)]
    simp [f4ShortY4, Fin.sum_univ_succ]
  | 4 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 4 1 0
        (by rw [f4Short_y4_up]; rfl) (by rw [f4Short_y4_down]; rfl)
        ![4] (by decide +kernel)]
    simp [f4ShortY4, Fin.sum_univ_succ]
  | 5 =>
    rw [f4Short_data.yOp_vec_eq ((mem_f4ShortSupport _).2 (Or.inr rfl)) t 5 0 0
        (by rw [f4Short_y4_up]; rfl) (by rw [f4Short_y4_down]; rfl)
        ![5] (by decide +kernel)]
    simp [f4ShortY4, Fin.sum_univ_succ]

theorem f4Short_Mat_y4 (t : K) :
    f4Short_data.Mat (yUnit Tag.F4 K (f4Index 3) t) = f4ShortY4 t :=
  f4Short_data.Mat_eq_of_col _ (fun b => by
    rw [coe_yUnit]
    exact f4Short_y4_cols t b)

theorem f4ShortX3_eq (t : K) : f4ShortX3 t = symCong (1 - t • single 1 0 1) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [f4ShortX3, symCong, symCoord, symMat, Matrix.mul_apply, Fin.sum_univ_three,
      Pi.single_apply, Matrix.single_apply] <;> ring

theorem f4ShortY3_eq (t : K) : f4ShortY3 t = symCong (1 - t • single 0 1 1) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [f4ShortY3, symCong, symCoord, symMat, Matrix.mul_apply, Fin.sum_univ_three,
      Pi.single_apply, Matrix.single_apply] <;> ring

theorem f4ShortX4_eq (t : K) : f4ShortX4 t = symCong (1 - t • single 2 1 1) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [f4ShortX4, symCong, symCoord, symMat, Matrix.mul_apply, Fin.sum_univ_three,
      Pi.single_apply, Matrix.single_apply] <;> ring

theorem f4ShortY4_eq (t : K) : f4ShortY4 t = symCong (1 - t • single 1 2 1) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [f4ShortY4, symCong, symCoord, symMat, Matrix.mul_apply, Fin.sum_univ_three,
      Pi.single_apply, Matrix.single_apply] <;> ring

end Mats

end CFSG.RankThree.PartOne.KF4
