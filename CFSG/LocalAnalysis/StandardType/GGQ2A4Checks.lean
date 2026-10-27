module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType

@[expose] def ggA4C : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2]

@[expose] def ggA4B (u v : Fin 4 → ZMod 3) : ZMod 3 :=
  ∑ i, ∑ j, u i * ggA4C i j * v j

@[expose] def ggA4Root : Fin 10 → Fin 4 → ZMod 3 :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 1, 0, 0], ![0, 1, 1, 0],
    ![0, 0, 1, 1], ![1, 1, 1, 0], ![0, 1, 1, 1], ![1, 1, 1, 1]]

@[expose] def ggA4RootWord : Fin 10 → List (Fin 4) :=
  ![[0], [1], [2], [3], [0, 1, 0], [1, 2, 1], [2, 3, 2], [0, 1, 2, 1, 0], [1, 2, 3, 2, 1],
    [0, 1, 2, 3, 2, 1, 0]]

@[expose] def ggA4F : Fin 5 → Fin 4 → ZMod 3 :=
  ![![2, 0, 1, 2], ![1, 0, 1, 2], ![1, 2, 1, 2], ![1, 2, 0, 2], ![1, 2, 0, 1]]

@[expose] def ggA4RAct (ε : ZMod 3) (m n : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  n - (ε * ggA4B m n) • m

@[expose] def ggA4WordAct (w : List (Fin 4)) (n : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  w.foldr (fun k v => ggA4RAct 1 (Pi.single k 1) v) n

@[expose] def ggA4NegWords : List (List (Fin 4)) :=
  [[2, 1, 0], [0, 2, 1], [1, 0, 2, 1, 0], [2, 1, 3], [3, 2, 1], [2, 1, 3, 2, 1]]

@[expose] def ggA4Cube (m : Fin 4 → ZMod 3) (w : List (Fin 4)) (n : Fin 4 → ZMod 3) :
    Fin 4 → ZMod 3 :=
  (fun v => ggA4RAct (-1) m (ggA4WordAct w v))^[3] n

@[expose] def ggA4Pi (i : Fin 4) : Fin 5 → Fin 5 :=
  Equiv.swap i.castSucc i.succ

theorem ggA4C_eq_cast : ∀ i j : Fin 4, ((CartanMatrix.A 4 i j : ℤ) : ZMod 3) = ggA4C i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem ggA4B_symm (u v : Fin 4 → ZMod 3) : ggA4B u v = ggA4B v u := by
  have hC : ∀ i j : Fin 4, ggA4C i j = ggA4C j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  simp only [ggA4B]
  calc ∑ i, ∑ j, u i * ggA4C i j * v j
      = ∑ i, ∑ j, u i * v j * ggA4C i j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ j, ∑ i, u j * v i * ggA4C j i := rfl
    _ = ∑ j, ∑ i, v i * u j * ggA4C i j := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [hC j i]
        ring
    _ = ∑ i, ∑ j, v i * u j * ggA4C i j := Finset.sum_comm
    _ = ∑ i, ∑ j, v i * ggA4C i j * u j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring

theorem ggA4B_single (i : Fin 4) (n : Fin 4 → ZMod 3) :
    ggA4B (Pi.single i 1) n = ∑ j, ggA4C i j * n j := by
  rw [ggA4B]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have h : (Pi.single i (1 : ZMod 3) : Fin 4 → ZMod 3) b = 0 := Pi.single_eq_of_ne hb 1
    simp [h]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem ggA4_nondeg : ∀ m : Fin 4 → ZMod 3, (∀ i : Fin 4, ggA4B (Pi.single i 1) m = 0) → m = 0 := by
  decide +kernel

theorem ggA4_root_norm : ∀ γ : Fin 10, ggA4B (ggA4Root γ) (ggA4Root γ) = 2 := by
  decide +kernel

theorem ggA4_root_simple : ∀ i : Fin 4, ggA4Root (Fin.castLE (by decide) i) = Pi.single i 1 := by
  decide +kernel

theorem ggA4_rootWord : ∀ γ : Fin 10, ∀ n : Fin 4 → ZMod 3,
    ggA4WordAct (ggA4RootWord γ) n = ggA4RAct 1 (ggA4Root γ) n := by
  decide +kernel

theorem ggA4_root_inj : ∀ γ δ : Fin 10,
    (∀ k : Fin 4, ggA4RAct 1 (ggA4Root γ) (Pi.single k 1) =
      ggA4RAct 1 (ggA4Root δ) (Pi.single k 1)) → γ = δ := by
  decide +kernel

theorem ggA4_conn_check : ∀ m : Fin 4 → ZMod 3, m ≠ 0 → ∀ γ δ : Fin 10,
    ggA4B (ggA4Root γ) m ≠ 0 → ggA4B (ggA4Root δ) m ≠ 0 →
    ggA4B (ggA4Root γ) (ggA4Root δ) ≠ 0 ∨
      ∃ ζ : Fin 10, ggA4B (ggA4Root ζ) m ≠ 0 ∧ ggA4B (ggA4Root γ) (ggA4Root ζ) ≠ 0 ∧
        ggA4B (ggA4Root ζ) (ggA4Root δ) ≠ 0 := by
  decide +kernel

theorem ggA4_norm_two : ∀ m : Fin 4 → ZMod 3, ggA4B m m = 2 →
    (∃ γ : Fin 10, m = ggA4Root γ ∨ m = -ggA4Root γ) ∨ ∃ k : Fin 5, m = ggA4F k ∨ m = -ggA4F k := by
  decide +kernel

theorem ggA4_norm_one : ∀ m : Fin 4 → ZMod 3, ggA4B m m = 1 →
    ∃ w ∈ ggA4NegWords, ∀ k : Fin 4, ggA4Cube m w (Pi.single k 1) = -Pi.single k 1 := by
  decide +kernel

theorem ggA4_F_norm : ∀ k : Fin 5, ggA4B (ggA4F k) (ggA4F k) = 2 := by
  decide +kernel

theorem ggA4_F_swap : ∀ (i : Fin 4) (k : Fin 5),
    ggA4RAct 1 (Pi.single i 1) (ggA4F k) = ggA4F (ggA4Pi i k) := by
  decide +kernel

theorem ggA4_F_swap_B : ∀ (i : Fin 4) (k : Fin 5) (n : Fin 4 → ZMod 3),
    ggA4B (ggA4F k) (ggA4RAct 1 (Pi.single i 1) n) = ggA4B (ggA4F (ggA4Pi i k)) n := by
  decide +kernel

theorem ggA4_pi_trans : ∀ S : Finset (Fin 5), S.Nonempty →
    (∀ (i : Fin 4) (k : Fin 5), k ∈ S → ggA4Pi i k ∈ S) → ∀ k, k ∈ S := by
  decide +kernel

theorem ggA4_line_check : ∀ μ : ZMod 3, μ ≠ 0 → ∀ n : Fin 4 → ZMod 3,
    10 ≤ (Finset.univ.filter (fun γ : Fin 10 => ggA4B (ggA4Root γ) n = 0)).card +
      (Finset.univ.filter (fun k : Fin 5 => μ + ggA4B (ggA4F k) n = 0)).card →
    n = 0 ∨ ∃ k : Fin 5, n = -(μ • ggA4F k) := by
  decide +kernel

theorem ggA5_restrict : ∀ i j : Fin 4,
    ((CartanMatrix.A 5 i.castSucc j.castSucc : ℤ) : ZMod 3) = ggA4C i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

end CFSG.StandardType

end
