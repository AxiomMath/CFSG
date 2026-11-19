module

public import CFSG.Quasithin.Background.RonanH49Base
public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr
open scoped Matrix

abbrev irrE (i j : Fin 3) : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.single i j 1

abbrev irrA : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

abbrev irrB : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

abbrev irrC : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

abbrev irrT0 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 0; 1, 0, 1]

abbrev irrT1 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 0; 0, 1, 1]

theorem irr_A_sq : irrA * irrA = 1 := by decide

theorem irr_B_sq : irrB * irrB = 1 := by decide

theorem irr_C_sq : irrC * irrC = 1 := by decide

theorem irr_T0_sq : irrT0 * irrT0 = 1 := by decide

theorem irr_T1_sq : irrT1 * irrT1 = 1 := by decide

theorem irr_add_self : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), X + X = 0 := by
  decide +kernel

theorem irr_inv_a : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), irrC * X * irrC = X →
    irrC * (irrA * X * irrA) * irrC = irrA * X * irrA := by
  decide +kernel

theorem irr_inv_b : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), irrC * X * irrC = X →
    irrA * X * irrA = X →
      irrC * (irrB * X * irrB) * irrC = irrB * X * irrB ∧
        irrA * (irrB * X * irrB) * irrA = irrB * X * irrB := by
  decide +kernel

theorem irr_fix : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), X.trace = 0 → irrC * X * irrC = X →
    irrA * X * irrA = X → irrB * X * irrB = X → X = 0 ∨ X = irrE 0 2 := by
  decide +kernel

theorem irr_decomp : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), X.trace = 0 →
    X = X 0 1 • irrE 0 1 + X 0 2 • irrE 0 2 + X 1 0 • irrE 1 0 + X 1 2 • irrE 1 2 +
      X 2 0 • irrE 2 0 + X 2 1 • irrE 2 1 +
      X 0 0 • (irrE 0 0 + irrE 2 2) + X 1 1 • (irrE 1 1 + irrE 2 2) := by
  decide +kernel

theorem irr_E_identity_D0 : irrE 0 0 + irrE 2 2 =
    irrE 2 0 + irrE 0 2 + irrT0 * irrE 0 2 * irrT0 := by
  decide

theorem irr_E_identity_D1 : irrE 1 1 + irrE 2 2 =
    irrE 2 1 + irrE 1 2 + irrT1 * irrE 1 2 * irrT1 := by
  decide

theorem irr_conj_add (g X Y : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    g * (X + Y) * g = g * X * g + g * Y * g := by
  simp only [Matrix.mul_add, Matrix.add_mul]

theorem irr_conj_conj (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hg : g * g = 1)
    (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) : g * (g * X * g) * g = X := by
  calc g * (g * X * g) * g = (g * g) * X * (g * g) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hg, Matrix.one_mul, Matrix.mul_one]

theorem irr_exists_fix (P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop)
    (hadd : ∀ X Y, P X → P Y → P (X + Y))
    (f : Matrix (Fin 3) (Fin 3) (ZMod 2) → Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hf_add : ∀ X Y, f (X + Y) = f X + f Y) (hff : ∀ X, f (f X) = X)
    (hfP : ∀ X, P X → P (f X)) {X : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hX : P X)
    (hX0 : X ≠ 0) : ∃ Y, P Y ∧ Y ≠ 0 ∧ f Y = Y := by
  by_cases hfX : f X = X
  · exact ⟨X, hX, hX0, hfX⟩
  · refine ⟨f X + X, hadd _ _ (hfP X hX) hX, fun h0 => hfX ?_, ?_⟩
    · have h1 : f X = -X := eq_neg_of_add_eq_zero_left h0
      rw [h1]
      exact neg_eq_iff_add_eq_zero.mpr (irr_add_self X)
    · rw [hf_add, hff, add_comm]

theorem irr_smul_mem (A : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2))) (c : ZMod 2)
    {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hB : B ∈ A) : c • B ∈ A := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · rw [zero_smul]
    exact A.zero_mem
  · rw [one_smul]
    exact hB

theorem irr_perm_mem (A : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hconj : ∀ g h : Matrix (Fin 3) (Fin 3) (ZMod 2), g * h = 1 → ∀ X ∈ A, g * X * h ∈ A)
    (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hP : P * Pᵀ = 1)
    {E F : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hE : E ∈ A) (hF : P * E * Pᵀ = F) : F ∈ A := by
  rw [← hF]
  exact hconj P Pᵀ hP E hE

theorem irr_matrix (A : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hconj : ∀ g h : Matrix (Fin 3) (Fin 3) (ZMod 2), g * h = 1 → ∀ X ∈ A, g * X * h ∈ A)
    (hA_tr : ∀ X ∈ A, X.trace = 0) (X0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hX0 : X0 ∈ A)
    (hX00 : X0 ≠ 0) : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), X.trace = 0 → X ∈ A := by
  obtain ⟨X1, hX1A, hX1ne, hX1c⟩ : ∃ Y, Y ∈ A ∧ Y ≠ 0 ∧ irrC * Y * irrC = Y :=
    irr_exists_fix (fun X => X ∈ A) (fun X Y hX hY => A.add_mem hX hY)
      (fun X => irrC * X * irrC) (fun X Y => irr_conj_add irrC X Y)
      (irr_conj_conj irrC irr_C_sq) (fun X hX => hconj _ _ irr_C_sq X hX) hX0 hX00
  obtain ⟨X2, ⟨hX2A, hX2c⟩, hX2ne, hX2a⟩ :
      ∃ Y, (Y ∈ A ∧ irrC * Y * irrC = Y) ∧ Y ≠ 0 ∧ irrA * Y * irrA = Y :=
    irr_exists_fix (fun X => X ∈ A ∧ irrC * X * irrC = X)
      (fun X Y hX hY => ⟨A.add_mem hX.1 hY.1, by rw [irr_conj_add, hX.2, hY.2]⟩)
      (fun X => irrA * X * irrA) (fun X Y => irr_conj_add irrA X Y)
      (irr_conj_conj irrA irr_A_sq)
      (fun X hX => ⟨hconj _ _ irr_A_sq X hX.1, irr_inv_a X hX.2⟩)
      (X := X1) ⟨hX1A, hX1c⟩ hX1ne
  obtain ⟨X3, ⟨⟨hX3A, hX3c⟩, hX3a⟩, hX3ne, hX3b⟩ :
      ∃ Y, ((Y ∈ A ∧ irrC * Y * irrC = Y) ∧ irrA * Y * irrA = Y) ∧ Y ≠ 0 ∧
        irrB * Y * irrB = Y :=
    irr_exists_fix (fun X => (X ∈ A ∧ irrC * X * irrC = X) ∧ irrA * X * irrA = X)
      (fun X Y hX hY => ⟨⟨A.add_mem hX.1.1 hY.1.1, by rw [irr_conj_add, hX.1.2, hY.1.2]⟩,
        by rw [irr_conj_add, hX.2, hY.2]⟩)
      (fun X => irrB * X * irrB) (fun X Y => irr_conj_add irrB X Y)
      (irr_conj_conj irrB irr_B_sq)
      (fun X hX => ⟨⟨hconj _ _ irr_B_sq X hX.1.1, (irr_inv_b X hX.1.2 hX.2).1⟩,
        (irr_inv_b X hX.1.2 hX.2).2⟩)
      (X := X2) ⟨⟨hX2A, hX2c⟩, hX2a⟩ hX2ne
  have hX3E : X3 = irrE 0 2 :=
    (irr_fix X3 (hA_tr X3 hX3A) hX3c hX3a hX3b).resolve_left hX3ne
  have hE02 : irrE 0 2 ∈ A := by
    rw [← hX3E]
    exact hX3A
  have hE01 : irrE 0 1 ∈ A :=
    irr_perm_mem A hconj !![1, 0, 0; 0, 0, 1; 0, 1, 0] (by decide) hE02 (by decide)
  have hE10 : irrE 1 0 ∈ A :=
    irr_perm_mem A hconj !![0, 0, 1; 1, 0, 0; 0, 1, 0] (by decide) hE02 (by decide)
  have hE12 : irrE 1 2 ∈ A :=
    irr_perm_mem A hconj !![0, 1, 0; 1, 0, 0; 0, 0, 1] (by decide) hE02 (by decide)
  have hE20 : irrE 2 0 ∈ A :=
    irr_perm_mem A hconj !![0, 0, 1; 0, 1, 0; 1, 0, 0] (by decide) hE02 (by decide)
  have hE21 : irrE 2 1 ∈ A :=
    irr_perm_mem A hconj !![0, 1, 0; 0, 0, 1; 1, 0, 0] (by decide) hE02 (by decide)
  have hD0 : irrE 0 0 + irrE 2 2 ∈ A := by
    rw [irr_E_identity_D0]
    exact A.add_mem (A.add_mem hE20 hE02) (hconj _ _ irr_T0_sq _ hE02)
  have hD1 : irrE 1 1 + irrE 2 2 ∈ A := by
    rw [irr_E_identity_D1]
    exact A.add_mem (A.add_mem hE21 hE12) (hconj _ _ irr_T1_sq _ hE12)
  intro X hX
  rw [irr_decomp X hX]
  exact A.add_mem (A.add_mem (A.add_mem (A.add_mem (A.add_mem (A.add_mem (A.add_mem
    (irr_smul_mem A _ hE01) (irr_smul_mem A _ hE02)) (irr_smul_mem A _ hE10))
    (irr_smul_mem A _ hE12)) (irr_smul_mem A _ hE20)) (irr_smul_mem A _ hE21))
    (irr_smul_mem A _ hD0)) (irr_smul_mem A _ hD1)

theorem irr_toAdd_eW (i j : Fin 3) : Multiplicative.toAdd (eW i j) = irrE i j := rfl

theorem irr_toAdd_dWd : Multiplicative.toAdd dWd = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  decide

theorem irr_mem_trZ {X : WMod} : X ∈ trZ ↔ Matrix.trace (Multiplicative.toAdd X) = 0 := by
  simp [trZ]

theorem trZ_ne_bot : trZ ≠ ⊥ := by
  intro h
  have hmem : eW 0 1 ∈ trZ := by
    rw [irr_mem_trZ, irr_toAdd_eW]
    decide
  rw [h, Subgroup.mem_bot] at hmem
  have h0 : irrE 0 1 = (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    have := congrArg Multiplicative.toAdd hmem
    rw [irr_toAdd_eW] at this
    exact this
  revert h0
  decide

theorem irr_hconj (U : Subgroup WMod) (hinv : ∀ l ∈ Cd, ∀ u ∈ U, l u ∈ U)
    (g h : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hgh : g * h = 1)
    (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hX : Multiplicative.ofAdd X ∈ U) :
    Multiplicative.ofAdd (g * X * h) ∈ U := by
  have hdet : g.det * h.det = 1 := by rw [← Matrix.det_mul, hgh, Matrix.det_one]
  have hg : g.det ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hdet
    exact zero_ne_one hdet
  have hh : h.det ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hdet
    exact zero_ne_one hdet
  have hht : (hᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hh
  have hpair : ∀ Y : Matrix (Fin 3) (Fin 3) (ZMod 2),
      Multiplicative.toAdd (rho (slOfMat g hg, slOfMat (hᵀ) hht) (Multiplicative.ofAdd Y)) =
        g * Y * h := by
    intro Y
    simp only [toAdd_rho, toAdd_ofAdd, mat_slOfMat, Matrix.transpose_transpose]
  have hfix : rho (slOfMat g hg, slOfMat (hᵀ) hht) dWd = dWd := by
    apply Multiplicative.toAdd.injective
    have h1 := hpair (Multiplicative.toAdd dWd)
    rw [ofAdd_toAdd] at h1
    rw [h1, irr_toAdd_dWd, Matrix.mul_one, hgh]
  have hl : rho (slOfMat g hg, slOfMat (hᵀ) hht) ∈ Cd :=
    mem_Cd.mpr ⟨img_le_norm (rho_mem_img _), hfix⟩
  rw [← hpair X, ofAdd_toAdd]
  exact hinv _ hl _ hX

theorem irred_trZ (U : Subgroup WMod) (hU : U ≤ trZ) (hinv : ∀ l ∈ Cd, ∀ u ∈ U, l u ∈ U) :
    U = ⊥ ∨ U = trZ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  refine Or.inr (le_antisymm hU ?_)
  rw [Subgroup.eq_bot_iff_forall] at hbot
  push Not at hbot
  obtain ⟨u, hu, hu1⟩ := hbot
  have hconj : ∀ g h : Matrix (Fin 3) (Fin 3) (ZMod 2), g * h = 1 →
      ∀ X ∈ Subgroup.toAddSubgroup' U, g * X * h ∈ Subgroup.toAddSubgroup' U := by
    intro g h hgh X hX
    rw [Subgroup.mem_toAddSubgroup'] at hX ⊢
    exact irr_hconj U hinv g h hgh X hX
  have hA_tr : ∀ X ∈ Subgroup.toAddSubgroup' U, X.trace = 0 := by
    intro X hX
    rw [Subgroup.mem_toAddSubgroup'] at hX
    have h := hU hX
    rwa [irr_mem_trZ, toAdd_ofAdd] at h
  have hu' : Multiplicative.toAdd u ∈ Subgroup.toAddSubgroup' U := by
    rw [Subgroup.mem_toAddSubgroup', ofAdd_toAdd]
    exact hu
  have hu0 : Multiplicative.toAdd u ≠ 0 := fun h0 =>
    hu1 (Multiplicative.toAdd.injective (h0.trans rfl))
  have hmat := irr_matrix (Subgroup.toAddSubgroup' U) hconj hA_tr _ hu' hu0
  intro x hx
  have h := hmat (Multiplicative.toAdd x) (irr_mem_trZ.mp hx)
  rw [Subgroup.mem_toAddSubgroup', ofAdd_toAdd] at h
  exact h

end CFSG.Quasithin.RonanH49
