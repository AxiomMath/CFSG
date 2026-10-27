module

public import CFSG.Quasithin.Background.JonesParshallSmallSL

public section

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall Matrix

@[expose] def t0M : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def s0M : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 1, 0, 0; 0, 1, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def gTM : Fin 5 → Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![0, 0, 1, 0, 0; 1, 1, 0, 1, 1; 0, 1, 1, 0, 1; 0, 0, 0, 0, 1; 0, 1, 0, 1, 0],
    !![0, 1, 0, 0, 0; 1, 0, 0, 1, 1; 0, 1, 0, 1, 0; 1, 1, 1, 1, 1; 1, 1, 1, 0, 0],
    !![0, 0, 1, 1, 1; 1, 0, 1, 0, 0; 0, 1, 1, 0, 0; 0, 1, 1, 1, 0; 1, 1, 0, 0, 1],
    !![0, 1, 0, 1, 0; 1, 1, 1, 1, 0; 1, 1, 0, 1, 0; 1, 0, 0, 0, 1; 1, 1, 0, 0, 0]]

@[expose] def gTMi : Fin 5 → Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![0, 1, 0, 1, 1; 1, 0, 1, 1, 0; 1, 0, 0, 0, 0; 1, 0, 1, 1, 1; 0, 0, 0, 1, 0],
    !![0, 1, 0, 1, 1; 1, 0, 0, 0, 0; 1, 1, 0, 1, 0; 1, 0, 1, 0, 0; 1, 0, 1, 1, 1],
    !![1, 0, 0, 1, 1; 1, 1, 1, 1, 1; 1, 1, 0, 1, 1; 0, 0, 1, 1, 0; 0, 1, 1, 0, 1],
    !![1, 0, 1, 0, 0; 1, 0, 1, 0, 1; 0, 1, 1, 0, 0; 0, 0, 1, 0, 1; 1, 0, 1, 1, 0]]

@[expose] def gSM : Fin 3 → Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![0, 0, 0, 1, 1; 1, 1, 1, 1, 0; 0, 1, 0, 1, 1; 0, 1, 0, 1, 0; 1, 1, 0, 1, 1],
    !![1, 1, 0, 1, 1; 0, 1, 0, 0, 1; 0, 0, 0, 1, 1; 1, 0, 1, 0, 1; 0, 1, 1, 0, 0]]

@[expose] def gSMi : Fin 3 → Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![0, 0, 1, 0, 1; 1, 0, 1, 0, 0; 0, 1, 1, 1, 1; 1, 0, 1, 1, 0; 0, 0, 1, 1, 0],
    !![0, 1, 0, 1, 1; 1, 1, 1, 1, 1; 1, 1, 1, 1, 0; 1, 0, 0, 1, 1; 1, 0, 1, 1, 1]]

@[expose] def wT : Fin 2 → List (Fin 5) :=
  ![[0],
    [3, 1, 3, 4, 3, 1, 3, 0, 2, 3, 4, 2, 4, 3, 0, 0, 1, 0, 2, 3, 2, 2, 0, 3, 4, 0, 2]]

@[expose] def wS : Fin 2 → List (Fin 3) :=
  ![[0, 2, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 1, 0, 1, 2, 2, 0, 2, 0, 2, 1, 2,
     0, 2, 0, 2],
    [1, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2,
     1, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 1, 2]]

theorem gTM_mul : ∀ i, gTM i * gTMi i = 1 := by decide

theorem gSM_mul : ∀ i, gSM i * gSMi i = 1 := by decide

theorem gTMi_mul : ∀ i, gTMi i * gTM i = 1 := by decide

theorem gSMi_mul : ∀ i, gSMi i * gSM i = 1 := by decide

theorem t0M_mul_self : t0M * t0M = 1 := by decide

theorem s0M_mul_self : s0M * s0M = 1 := by decide

set_option maxRecDepth 100000 in
theorem wT_spec : ∀ k, wordEvalM (fun i => gTM i * t0M * gTMi i) (wT k) = mats5 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wS_spec : ∀ k, wordEvalM (fun i => gSM i * s0M * gSMi i) (wS k) = mats5 k := by
  decide +kernel

theorem det_eq_one_of_mul {M M' : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : M * M' = 1) :
    M.det = 1 := by
  have h1 : M.det * M'.det = 1 := by rw [← det_mul, h, det_one]
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) M.det with h0 | h0
  · rw [h0, zero_mul] at h1
    exact absurd h1 (by decide)
  · exact h0

@[expose] def ofMatInv (M M' : Matrix (Fin 5) (Fin 5) (ZMod 2)) (h : M * M' = 1) :
    SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨M, det_eq_one_of_mul h⟩

theorem ofMatInv_mul {M M' : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : M * M' = 1)
    (h' : M' * M = 1) : ofMatInv M M' h * ofMatInv M' M h' = 1 :=
  Subtype.ext h

theorem inv_ofMatInv {M M' : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : M * M' = 1)
    (h' : M' * M = 1) : (ofMatInv M M' h)⁻¹ = ofMatInv M' M h' :=
  inv_eq_of_mul_eq_one_right (ofMatInv_mul h h')

@[expose] def t0 : SpecialLinearGroup (Fin 5) (ZMod 2) := ofMatInv t0M t0M t0M_mul_self

@[expose] def s0 : SpecialLinearGroup (Fin 5) (ZMod 2) := ofMatInv s0M s0M s0M_mul_self

@[expose] def gT (i : Fin 5) : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ofMatInv (gTM i) (gTMi i) (gTM_mul i)

@[expose] def gS (i : Fin 3) : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ofMatInv (gSM i) (gSMi i) (gSM_mul i)

theorem coe_gT_conj (i : Fin 5) :
    ((gT i * t0 * (gT i)⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) = gTM i * t0M * gTMi i := by
  rw [gT, inv_ofMatInv (gTM_mul i) (gTMi_mul i)]
  rfl

theorem coe_gS_conj (i : Fin 3) :
    ((gS i * s0 * (gS i)⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) = gSM i * s0M * gSMi i := by
  rw [gS, inv_ofMatInv (gSM_mul i) (gSMi_mul i)]
  rfl

theorem closure_eq_top_of_words {k : ℕ}
    (c : Fin k → SpecialLinearGroup (Fin 5) (ZMod 2)) (w : Fin 2 → List (Fin k))
    (hw : ∀ j, wordEvalM (fun i => (c i : Matrix (Fin 5) (Fin 5) (ZMod 2))) (w j) = mats5 j) :
    Subgroup.closure (Set.range c) = ⊤ := by
  have htop : Subgroup.closure (Set.range gens5) = ⊤ :=
    closure_range_eq_top (tw := tw5) (by rw [gens5_coe]; exact tw5_spec)
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  have h : gens5 j = wordEval c (w j) := by
    apply Subtype.ext
    rw [coe_wordEval, hw j]
    exact congrFun gens5_coe j
  rw [h]
  exact wordEval_mem_closure c (w j)

theorem closure_t0 :
    Subgroup.closure (Set.range fun i : Fin 5 => gT i * t0 * (gT i)⁻¹) = ⊤ :=
  closure_eq_top_of_words _ wT fun j => by
    simp only [coe_gT_conj]
    exact wT_spec j

theorem closure_s0 :
    Subgroup.closure (Set.range fun i : Fin 3 => gS i * s0 * (gS i)⁻¹) = ⊤ :=
  closure_eq_top_of_words _ wS fun j => by
    simp only [coe_gS_conj]
    exact wS_spec j

end CFSG.Quasithin.B42Ln
