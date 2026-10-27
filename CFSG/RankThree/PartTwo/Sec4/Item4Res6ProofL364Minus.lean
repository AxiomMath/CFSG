module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Toral

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res6L364

open CFSG CFSG.LieType.Seitz CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

@[expose] def f4 : Fin 4 → F4 := ![0, 1, ω4, ω4 * ω4]

@[expose] def mat (t : Matrix (Fin 3) (Fin 3) (Fin 4)) : Matrix (Fin 3) (Fin 3) F4 := t.map f4

@[expose] def zyLab (a : Fin 3) : Lab := (mulLab zLab (wLab a)).1

@[expose] def z2yLab (a : Fin 3) : Lab := (mulLab (mulLab zLab zLab).1 (wLab a)).1

@[expose] def WordOK (g : Fin 4 → Matrix (Fin 3) (Fin 3) (Fin 4)) (d : Fin 4 → Lab)
    (i j : Fin 3) (c l : Fin 4) : Prop :=
  (∀ k, (mat (g k)).det = 1) ∧
  (∀ k, ∃ m : F4, m ≠ 0 ∧ mat (g k) * L (d k) = m • (L (d k) * mat (g k))) ∧
  mat (g 0) * mat (g 1) * mat (g 2) * mat (g 3) = f4 l • Matrix.transvection i j (f4 c)

instance (g : Fin 4 → Matrix (Fin 3) (Fin 3) (Fin 4)) (d : Fin 4 → Lab) (i j : Fin 3)
    (c l : Fin 4) : Decidable (WordOK g d i j c l) := by
  unfold WordOK; infer_instance

@[expose] def wT : Matrix (Fin 3) (Fin 3) (Fin 4) := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem word11 : WordOK ![wT, !![0, 1, 1; 1, 0, 3; 1, 2, 0], !![0, 1, 1; 1, 0, 2; 2, 2, 0],
    !![0, 1, 1; 2, 0, 2; 2, 1, 0]] ![zLab, wLab 1, z2yLab 1, zyLab 1] 2 0 2 1 := by
  decide +kernel

theorem word12 : WordOK ![wT, !![1, 1, 1; 1, 1, 3; 1, 2, 1], !![1, 1, 2; 1, 1, 1; 3, 1, 1],
    !![1, 1, 3; 3, 3, 1; 3, 1, 2]] ![zLab, wLab 1, z2yLab 1, zyLab 1] 1 0 3 2 := by
  decide +kernel

theorem word21 : WordOK ![wT, !![0, 1, 1; 1, 0, 2; 1, 3, 0], !![0, 1, 1; 1, 0, 3; 3, 3, 0],
    !![0, 1, 1; 3, 0, 3; 3, 1, 0]] ![zLab, wLab 2, zyLab 2, z2yLab 2] 2 0 3 1 := by
  decide +kernel

theorem word22 : WordOK ![wT, !![1, 1, 1; 1, 1, 2; 1, 3, 1], !![1, 1, 3; 1, 1, 1; 2, 1, 1],
    !![1, 1, 2; 2, 2, 1; 2, 1, 3]] ![zLab, wLab 2, zyLab 2, z2yLab 2] 1 0 2 3 := by
  decide +kernel

theorem ρ_zy_mem {E : Subgroup (MulAut Y64)} {a : Fin 3} (hz : ρ zLab ∈ E)
    (hy : ρ (wLab a) ∈ E) : ρ (zyLab a) ∈ E ∧ ρ (z2yLab a) ∈ E := by
  refine ⟨?_, ?_⟩
  · rw [zyLab, ← ρ_mul]; exact E.mul_mem hz hy
  · rw [z2yLab, ← ρ_mul, ← ρ_mul]; exact E.mul_mem (E.mul_mem hz hz) hy

theorem slι_mul4 (A B C D : Matrix (Fin 3) (Fin 3) F4) (hA : A.det = 1) (hB : B.det = 1)
    (hC : C.det = 1) (hD : D.det = 1) (h : (A * B * C * D).det = 1) :
    slι (A * B * C * D) h = slι A hA * slι B hB * slι C hC * slι D hD := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_slι, Matrix.map_mul]

theorem tv_mem_of_word {E : Subgroup (MulAut Y64)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (h27 : Nat.card E = 27) (hf : fieldAut 3 K64 σ4 ∈ E)
    {g : Fin 4 → Matrix (Fin 3) (Fin 3) (Fin 4)} {d : Fin 4 → Lab} {i j : Fin 3} {c l : Fin 4}
    (hW : WordOK g d i j c l) (hd : ∀ k, ρ (d k) ∈ E) (hd0 : ∀ k, d k ≠ (0, 0, 0))
    (hij : i ≠ j) (hl : f4 l ≠ 0) :
    tv hij (ι (f4 c)) ∈ (seitzHyperGamma 3 E).comap (proj 3 K64) := by
  obtain ⟨hdet, hcomm, hprod⟩ := hW
  have hfac : ∀ k, proj 3 K64 (slι (mat (g k)) (hdet k)) ∈ seitzHyperGamma 3 E := by
    intro k
    obtain ⟨m, hm, hmk⟩ := hcomm k
    exact mem_H_of_fixed hE h27 (hd k) hf (ρ_mem _) (ρ_ne_one (hd0 k)) fieldAut_σ4_not_mem
      (ρ_proj_slι _ hm hmk) (fieldAut_proj_slι _ _)
  have hdet4 : (mat (g 0) * mat (g 1) * mat (g 2) * mat (g 3)).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hdet, hdet, hdet, hdet]; simp
  have hmem : proj 3 K64 (slι _ hdet4) ∈ seitzHyperGamma 3 E := by
    rw [slι_mul4 _ _ _ _ (hdet 0) (hdet 1) (hdet 2) (hdet 3), map_mul, map_mul, map_mul]
    exact mul_mem (mul_mem (mul_mem (hfac 0) (hfac 1)) (hfac 2)) (hfac 3)
  have htv := slι_transvection hij (f4 c)
  have heq : proj 3 K64 (slι _ hdet4) =
      proj 3 K64 (slι (Matrix.transvection i j (f4 c)) (Matrix.det_transvection_of_ne i j hij _)) :=
    proj_scalar_mul (f4 l) hl _ _ (by
      rw [coe_slι, coe_slι, hprod]
      ext a b
      simp [map_mul])
  rw [heq, htv] at hmem
  exact hmem

theorem L_wLab (a : Fin 3) : L (wLab a) = !![0, 0, 1; 1, 0, 0; 0, ω4 ^ (a : ℕ), 0] := by
  revert a
  decide

theorem ρ_proj_diag_shift (a : Fin 3) (d : Fin 3 → K64) (h : d 0 * d 1 * d 2 = 1) :
    ρ (wLab a) (proj 3 K64 (diagSL3 d h)) =
      proj 3 K64 (diagSL3 ![d 2, d 0, d 1] (by simp; rw [← h]; ring)) := by
  rw [ρ, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  set A : Matrix (Fin 3) (Fin 3) K64 :=
    ((glι (LGL (wLab a)) : GL (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64) with hA
  have hAm : A = !![0, 0, 1; 1, 0, 0; 0, ι (ω4 ^ (a : ℕ)), 0] := by
    rw [hA, coe_glι, coe_LGL, L_wLab]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hcomm : A * diagonal d = diagonal ![d 2, d 0, d 1] * A := by
    rw [hAm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Matrix.diagonal_apply]; try ring)
  change A * diagonal d * _ = diagonal ![d 2, d 0, d 1]
  rw [hcomm, Matrix.mul_assoc, hA, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

theorem fieldAut_proj_diag (d : Fin 3 → K64) (h : d 0 * d 1 * d 2 = 1) :
    fieldAut 3 K64 σ4 (proj 3 K64 (diagSL3 d h)) =
      proj 3 K64 (diagSL3 (fun k => σ4 (d k)) (by rw [← map_mul, ← map_mul, h, map_one])) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext a b
  change σ4 ((diagonal d) a b) = (diagonal fun k => σ4 (d k)) a b
  simp only [Matrix.diagonal_apply]
  split_ifs <;> simp

theorem b7_prod : b7 * b7 ^ 4 * b7 ^ 2 = 1 := by
  rw [← pow_succ', ← pow_add]; exact b7_pow

theorem diagSL3_congr {d d' : Fin 3 → K64} (h : d 0 * d 1 * d 2 = 1) (h' : d' 0 * d' 1 * d' 2 = 1)
    (hd : ∀ k, d k = d' k) : diagSL3 d h = diagSL3 d' h' := by
  apply Subtype.ext
  change diagonal d = diagonal d'
  rw [funext hd]

@[expose] noncomputable def tSL : SpecialLinearGroup (Fin 3) K64 :=
  diagSL3 ![b7, b7 ^ 4, b7 ^ 2] (by simpa using b7_prod)

@[expose] noncomputable def zSL : SpecialLinearGroup (Fin 3) K64 :=
  diagSL3 ![1, ω, ω ^ 2] (by simp [← pow_succ', omega_cube])

theorem wSL_eq : wSL = slι (mat wT) (by decide) := by
  apply Subtype.ext
  rw [coe_wSL, coe_slι]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wK, mat, wT, f4]

theorem tSL_mem {E : Subgroup (MulAut Y64)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (h27 : Nat.card E = 27) (hf : fieldAut 3 K64 σ4 ∈ E) {a : Fin 3} (hz : ρ zLab ∈ E)
    (hy : ρ (wLab a) ∈ E) : tSL ∈ (seitzHyperGamma 3 E).comap (proj 3 K64) := by
  refine mem_H_of_fixed hE h27 hz (E.mul_mem hf hy) (ρ_mem _) (ρ_ne_one (by decide)) ?_
    (ρ_proj_diag _ _) ?_
  · intro hmem
    exact fieldAut_σ4_not_mem (by
      have := mul_mem hmem (inv_mem (ρ_mem (wLab a)))
      rwa [mul_inv_cancel_right] at this)
  · rw [MulAut.mul_apply, tSL, ρ_proj_diag_shift, fieldAut_proj_diag]
    congr 1
    apply diagSL3_congr
    intro k
    fin_cases k
    · change σ4 (b7 ^ 2) = b7
      rw [σ4_apply, ← pow_mul, show 2 * 4 = 7 + 1 by norm_num, pow_succ, b7_pow, one_mul]
    · change σ4 b7 = b7 ^ 4
      rw [σ4_apply]
    · change σ4 (b7 ^ 4) = b7 ^ 2
      rw [σ4_apply, ← pow_mul, show 4 * 4 = 7 * 2 + 2 by norm_num, pow_add, pow_mul, b7_pow,
        one_pow, one_mul]

theorem zSL_mem {E : Subgroup (MulAut Y64)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (h27 : Nat.card E = 27) (hf : fieldAut 3 K64 σ4 ∈ E) (hz : ρ zLab ∈ E) :
    zSL ∈ (seitzHyperGamma 3 E).comap (proj 3 K64) := by
  refine mem_H_of_fixed hE h27 hz hf (ρ_mem _) (ρ_ne_one (by decide)) fieldAut_σ4_not_mem
    (ρ_proj_diag _ _) ?_
  rw [zSL, fieldAut_proj_diag]
  congr 1
  apply diagSL3_congr
  intro k
  fin_cases k
  · change σ4 1 = 1; exact map_one σ4
  · change σ4 ω = ω; exact σ4_omega
  · change σ4 (ω ^ 2) = ω ^ 2; rw [map_pow, σ4_omega]

theorem wSL_mem {E : Subgroup (MulAut Y64)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (h27 : Nat.card E = 27) (hf : fieldAut 3 K64 σ4 ∈ E) (hz : ρ zLab ∈ E) :
    wSL ∈ (seitzHyperGamma 3 E).comap (proj 3 K64) := by
  rw [wSL_eq]
  have hc : ∃ m : F4, m ≠ 0 ∧ mat wT * L zLab = m • (L zLab * mat wT) := by decide
  obtain ⟨m, hm, hmw⟩ := hc
  exact mem_H_of_fixed hE h27 hz hf (ρ_mem _) (ρ_ne_one (by decide)) fieldAut_σ4_not_mem
    (ρ_proj_slι _ hm hmw) (fieldAut_proj_slι _ _)

theorem ι_f4_ne_zero {c : Fin 4} (hc : c ≠ 0) : ι (f4 c) ≠ 0 := by
  rw [Ne, map_eq_zero_iff ι ι_injective]
  revert c; decide

theorem b7_cube_ne_one : b7 ^ 3 ≠ 1 := by
  intro h
  have := seven_dvd_of_pow_eq_one b7_pow b7_ne_one h
  norm_num at this

theorem seitzHyperGamma_eq_top_minus {E : Subgroup (MulAut Y64)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27)
    (hf : fieldAut 3 K64 σ4 ∈ E) {a : Fin 3} (ha : a ≠ 0) (hz : ρ zLab ∈ E)
    (hy : ρ (wLab a) ∈ E) : seitzHyperGamma 3 E = ⊤ := by
  set H := (seitzHyperGamma 3 E).comap (proj 3 K64) with hH
  obtain ⟨hzy, hz2y⟩ := ρ_zy_mem hz hy
  have hT := tSL_mem hE h27 hf hz hy
  have hZ := zSL_mem hE h27 hf hz
  have hW := wSL_mem hE h27 hf hz
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have key : ∃ c₁ c₂ : Fin 4, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ tv h20 (ι (f4 c₁)) ∈ H ∧
      tv h10 (ι (f4 c₂)) ∈ H := by
    have ha' : a = 1 ∨ a = 2 := (by decide : ∀ b : Fin 3, b ≠ 0 → b = 1 ∨ b = 2) a ha
    rcases ha' with rfl | rfl
    · refine ⟨2, 3, by decide, by decide, tv_mem_of_word hE h27 hf word11 ?_ ?_ h20 (by decide),
        tv_mem_of_word hE h27 hf word12 ?_ ?_ h10 (by decide)⟩
      · intro k; fin_cases k
        exacts [hz, hy, hz2y, hzy]
      · intro k; fin_cases k <;> decide
      · intro k; fin_cases k
        exacts [hz, hy, hz2y, hzy]
      · intro k; fin_cases k <;> decide
    · refine ⟨3, 2, by decide, by decide, tv_mem_of_word hE h27 hf word21 ?_ ?_ h20 (by decide),
        tv_mem_of_word hE h27 hf word22 ?_ ?_ h10 (by decide)⟩
      · intro k; fin_cases k
        exacts [hz, hy, hzy, hz2y]
      · intro k; fin_cases k <;> decide
      · intro k; fin_cases k
        exacts [hz, hy, hzy, hz2y]
      · intro k; fin_cases k <;> decide
  obtain ⟨c₁, c₂, hc₁, hc₂, h₁, h₂⟩ := key
  have hzSL : ((zSL : SpecialLinearGroup (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64) =
      diagonal ![1, ω, ω ^ 2] := rfl
  have htSL : ((tSL : SpecialLinearGroup (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64) =
      diagonal ![b7, b7 ^ 4, b7 ^ 2] := rfl
  have hall20 : ∀ c, tv h20 c ∈ H := by
    refine forall_tv_mem h20 (ι_f4_ne_zero hc₁) h₁ hzSL htSL hZ hT (by simp) (by simp [b7_ne_zero])
      ?_ ?_ ?_
    · simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Matrix.cons_val_zero, div_one]
      linear_combination ω * omega_cube + omega_sq_add
    · simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Matrix.cons_val_zero]
      rw [pow_two, mul_div_cancel_right₀ _ b7_ne_zero]; exact b7_pow
    · simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Matrix.cons_val_zero]
      rw [pow_two, mul_div_cancel_right₀ _ b7_ne_zero]; exact b7_ne_one
  have hall10 : ∀ c, tv h10 c ∈ H := by
    refine forall_tv_mem h10 (ι_f4_ne_zero hc₂) h₂ hzSL htSL hZ hT (by simp) (by simp [b7_ne_zero])
      ?_ ?_ ?_
    · simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, div_one]
      exact omega_sq_add
    · simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [show b7 ^ 4 = b7 ^ 3 * b7 by ring, mul_div_cancel_right₀ _ b7_ne_zero, ← pow_mul,
        show 3 * 7 = 7 * 3 by norm_num, pow_mul, b7_pow, one_pow]
    · simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [show b7 ^ 4 = b7 ^ 3 * b7 by ring, mul_div_cancel_right₀ _ b7_ne_zero]
      exact b7_cube_ne_one
  have htop := eq_top_of_orbits hW hall20 hall10
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := proj_surjective 3 K64 x
  have : g ∈ H := by rw [hH, htop]; trivial
  exact this

end CFSG.RankThree.PartTwo.Sec4.Res6L364
