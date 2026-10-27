module

public import CFSG.RankThree.PartOne.KF4.B2Data
public import CFSG.RankThree.PartOne.KF4.B2Sp
public import CFSG.RankThree.PartOne.KF4.Torus2

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped Pointwise

namespace MinNativeData

variable {τ : Tag} {n : ℕ} {J : Set (Fin τ.rank)} {w : Fin n → Fin τ.rank → ℤ}
  (D : MinNativeData τ n J w) {K : Type} [Field K]

theorem Mat_xUnit_pair {i : Fin τ.rank} (hi : i ∈ J) {p q p' q' : Fin n}
    (hpq : ∀ a b : Fin n, w b + Pi.single i 1 = w a ↔ ((a = p ∧ b = q) ∨ (a = p' ∧ b = q')))
    (hne : ¬(p = p' ∧ q = q')) (t : K) :
    D.Mat (xUnit τ K i t) = 1 + (Matrix.single p q t + Matrix.single p' q' t) := by
  rw [D.Mat_xUnit hi]
  congr 1
  ext a b
  rw [Matrix.smul_apply, nPlus, Matrix.of_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply]
  by_cases h : w b + Pi.single i 1 = w a
  · rcases (hpq a b).1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h' : ¬(p' = a ∧ q' = b) := fun e => hne ⟨h1.symm.trans e.1.symm, h2.symm.trans e.2.symm⟩
      subst h1 h2
      simp [h, h']
    · have h' : ¬(p = a ∧ q = b) := fun e => hne ⟨e.1.trans h1, e.2.trans h2⟩
      subst h1 h2
      simp [h, h']
  · have h1 : ¬(p = a ∧ q = b) := fun e => h ((hpq a b).2 (Or.inl ⟨e.1.symm, e.2.symm⟩))
    have h2 : ¬(p' = a ∧ q' = b) := fun e => h ((hpq a b).2 (Or.inr ⟨e.1.symm, e.2.symm⟩))
    simp [h, h1, h2]

theorem Mat_yUnit_pair {i : Fin τ.rank} (hi : i ∈ J) {p q p' q' : Fin n}
    (hpq : ∀ a b : Fin n, w b - Pi.single i 1 = w a ↔ ((a = p ∧ b = q) ∨ (a = p' ∧ b = q')))
    (hne : ¬(p = p' ∧ q = q')) (t : K) :
    D.Mat (yUnit τ K i t) = 1 + (Matrix.single p q t + Matrix.single p' q' t) := by
  rw [D.Mat_yUnit hi]
  congr 1
  ext a b
  rw [Matrix.smul_apply, nMinus, Matrix.of_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply]
  by_cases h : w b - Pi.single i 1 = w a
  · rcases (hpq a b).1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h' : ¬(p' = a ∧ q' = b) := fun e => hne ⟨h1.symm.trans e.1.symm, h2.symm.trans e.2.symm⟩
      subst h1 h2
      simp [h, h']
    · have h' : ¬(p = a ∧ q = b) := fun e => hne ⟨e.1.trans h1, e.2.trans h2⟩
      subst h1 h2
      simp [h, h']
  · have h1 : ¬(p = a ∧ q = b) := fun e => h ((hpq a b).2 (Or.inl ⟨e.1.symm, e.2.symm⟩))
    have h2 : ¬(p' = a ∧ q' = b) := fun e => h ((hpq a b).2 (Or.inr ⟨e.1.symm, e.2.symm⟩))
    simp [h, h1, h2]

end MinNativeData

section SpLemmas

variable {K : Type} [Field K]

private theorem sp_x2 (c : K) :
    (1 + single (1 : Fin 4) 2 c)ᵀ * f4B2J0 K * (1 + single (1 : Fin 4) 2 c) = f4B2J0 K := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [f4B2J0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply,
      Matrix.one_apply]

private theorem sp_y2 (c : K) :
    (1 + single (2 : Fin 4) 1 c)ᵀ * f4B2J0 K * (1 + single (2 : Fin 4) 1 c) = f4B2J0 K := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [f4B2J0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply,
      Matrix.one_apply]

private theorem sp_x3 (c : K) :
    (1 + (single (0 : Fin 4) 1 c + single (2 : Fin 4) 3 c))ᵀ * f4B2J0 K *
      (1 + (single (0 : Fin 4) 1 c + single (2 : Fin 4) 3 c)) = f4B2J0 K := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [f4B2J0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply,
      Matrix.one_apply]

private theorem sp_y3 (c : K) :
    (1 + (single (1 : Fin 4) 0 c + single (3 : Fin 4) 2 c))ᵀ * f4B2J0 K *
      (1 + (single (1 : Fin 4) 0 c + single (3 : Fin 4) 2 c)) = f4B2J0 K := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [f4B2J0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply,
      Matrix.one_apply]

end SpLemmas

section Mats

variable {K : Type} [Field K]

theorem f4B2_Mat_x2 (t : K) :
    f4B2_data.Mat (xUnit Tag.F4 K (f4Index 1) t) = 1 + single 1 2 t :=
  f4B2_data.Mat_xUnit_single ((mem_f4B2Support _).2 (Or.inl rfl)) f4B2_steps.1 t

theorem f4B2_Mat_y2 (t : K) :
    f4B2_data.Mat (yUnit Tag.F4 K (f4Index 1) t) = 1 + single 2 1 t :=
  f4B2_data.Mat_yUnit_single ((mem_f4B2Support _).2 (Or.inl rfl)) f4B2_steps.2.1 t

theorem f4B2_Mat_x3 (t : K) :
    f4B2_data.Mat (xUnit Tag.F4 K (f4Index 2) t) = 1 + (single 0 1 t + single 2 3 t) :=
  f4B2_data.Mat_xUnit_pair ((mem_f4B2Support _).2 (Or.inr rfl)) f4B2_steps.2.2.1
    (by decide) t

theorem f4B2_Mat_y3 (t : K) :
    f4B2_data.Mat (yUnit Tag.F4 K (f4Index 2) t) = 1 + (single 1 0 t + single 3 2 t) :=
  f4B2_data.Mat_yUnit_pair ((mem_f4B2Support _).2 (Or.inr rfl)) f4B2_steps.2.2.2
    (by decide) t

theorem torusElt_mem_f4B2 {i : Fin Tag.F4.rank} (hi : i ∈ f4B2Support) (a : Kˣ) :
    torusElt Tag.F4 K i a ∈ subsystemGroup Tag.F4 K f4B2Support :=
  subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi a)

theorem torus2Elt_mem_f4B2 (a b : Kˣ) :
    torus2Elt (f4Index 1) (f4Index 2) a b ∈ subsystemGroup Tag.F4 K f4B2Support :=
  mul_mem (torusElt_mem_f4B2 ((mem_f4B2Support _).2 (Or.inl rfl)) a)
    (torusElt_mem_f4B2 ((mem_f4B2Support _).2 (Or.inr rfl)) b)

theorem f4B2_Mat_torus (a b : Kˣ) :
    f4B2_data.Mat (torus2Elt (f4Index 1) (f4Index 2) a b) =
      Matrix.diagonal ![(b : K), ((a * b⁻¹ : Kˣ) : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] := by
  rw [torus2Elt,
    f4B2_data.Mat_mul (torusElt_mem_f4B2 ((mem_f4B2Support _).2 (Or.inl rfl)) a)
      (torusElt_mem_f4B2 ((mem_f4B2Support _).2 (Or.inr rfl)) b),
    f4B2_data.Mat_torusElt, f4B2_data.Mat_torusElt, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  obtain ⟨h0, h2⟩ := f4B2_pairing k
  rw [h0, h2]
  fin_cases k <;> simp [Units.val_mul, _root_.zpow_neg]

theorem f4B2_Mat_mem_Sp {g : ModGL Tag.F4 K} (hg : g ∈ subsystemGroup Tag.F4 K f4B2Support) :
    (f4B2_data.Mat g)ᵀ * f4B2J0 K * f4B2_data.Mat g = f4B2J0 K := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_f4B2Support i).1 hi with rfl | rfl
      · rw [f4B2_Mat_x2]; exact sp_x2 c
      · rw [f4B2_Mat_x3]; exact sp_x3 c
    · rcases (mem_f4B2Support i).1 hi with rfl | rfl
      · rw [f4B2_Mat_y2]; exact sp_y2 c
      · rw [f4B2_Mat_y3]; exact sp_y3 c
  | one =>
    rw [f4B2_data.Mat_one, transpose_one, Matrix.one_mul, Matrix.mul_one]
  | mul x y hx hy ihx ihy =>
    rw [f4B2_data.Mat_mul hx hy, transpose_mul]
    calc (f4B2_data.Mat y)ᵀ * (f4B2_data.Mat x)ᵀ * f4B2J0 K * (f4B2_data.Mat x * f4B2_data.Mat y)
        = (f4B2_data.Mat y)ᵀ * ((f4B2_data.Mat x)ᵀ * f4B2J0 K * f4B2_data.Mat x) *
            f4B2_data.Mat y := by simp only [Matrix.mul_assoc]
      _ = f4B2J0 K := by rw [ihx, ihy]
  | inv x hx ih =>
    have h := f4B2_data.Mat_mul (inv_mem hx) hx
    rw [inv_mul_cancel, f4B2_data.Mat_one] at h
    calc (f4B2_data.Mat x⁻¹)ᵀ * f4B2J0 K * f4B2_data.Mat x⁻¹
        = (f4B2_data.Mat x⁻¹)ᵀ * ((f4B2_data.Mat x)ᵀ * f4B2J0 K * f4B2_data.Mat x) *
            f4B2_data.Mat x⁻¹ := by rw [ih]
      _ = (f4B2_data.Mat x * f4B2_data.Mat x⁻¹)ᵀ * f4B2J0 K *
            (f4B2_data.Mat x * f4B2_data.Mat x⁻¹) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = f4B2J0 K := by
          have h' : f4B2_data.Mat x * f4B2_data.Mat x⁻¹ = 1 := by
            rw [← f4B2_data.Mat_mul hx (inv_mem hx), mul_inv_cancel, f4B2_data.Mat_one]
          rw [h', transpose_one, Matrix.one_mul, Matrix.mul_one]

variable (K) in
@[expose] def f4B2Mat : subsystemGroup Tag.F4 K f4B2Support →* Matrix (Fin 4) (Fin 4) K where
  toFun g := f4B2_data.Mat (g : ModGL Tag.F4 K)
  map_one' := f4B2_data.Mat_one
  map_mul' g h := f4B2_data.Mat_mul g.2 h.2

variable (K) in
@[expose] def f4B2RepGL : subsystemGroup Tag.F4 K f4B2Support →* GL (Fin 4) K :=
  (f4B2Mat K).toHomUnits

variable (K) in
@[expose] def f4B2Rep : subsystemGroup Tag.F4 K f4B2Support →* f4SpGroup K :=
  (f4B2RepGL K).codRestrict (f4SpGroup K) fun g => f4B2_Mat_mem_Sp g.2

theorem coe_f4B2Rep (g : subsystemGroup Tag.F4 K f4B2Support) :
    (((f4B2Rep K g : f4SpGroup K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      f4B2_data.Mat (g : ModGL Tag.F4 K) :=
  rfl

end Mats

end CFSG.RankThree.PartOne.KF4
