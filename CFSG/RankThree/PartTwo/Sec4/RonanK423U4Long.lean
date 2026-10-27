module

public import CFSG.RankThree.PartTwo.Sec21.KS21U4Blocks
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423

open Matrix CFSG CFSG.RankThree.PartTwo.Sec21.U4Lines
open CFSG.LieType.Universal.Unitary (SU mem_SU conjTr antidiag)

variable {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F)

omit [Finite F] [CharP F 2] in
theorem diagonal_mul_diagonal_eq_one {d e : Fin 4 → F} (h : ∀ i, d i * e i = 1) :
    diagonal d * diagonal e = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact h i

omit [Finite F] [CharP F 2] in
@[expose] noncomputable def u4lDiag (d e : Fin 4 → F) (h : ∀ i, d i * e i = 1) :
    GL (Fin 4) F :=
  ⟨diagonal d, diagonal e, diagonal_mul_diagonal_eq_one h,
    diagonal_mul_diagonal_eq_one fun i => (mul_comm _ _).trans (h i)⟩

omit [Finite F] [CharP F 2] in
theorem u4l_sigma_ne_zero {x : F} (hx : x ≠ 0) : σ x ≠ 0 := by
  intro h
  apply hx
  apply σ.injective
  rw [h, map_zero]

omit [Finite F] [CharP F 2] in
@[expose] def u4lPsiD (c : Fˣ) : Fin 4 → F :=
  ![(c : F) ^ 2, σ (c : F) / (c : F), σ (c : F) / (c : F), (σ (c : F) ^ 2)⁻¹]

omit [Finite F] [CharP F 2] in
@[expose] def u4lPsiE (c : Fˣ) : Fin 4 → F :=
  ![((c : F) ^ 2)⁻¹, (c : F) / σ (c : F), (c : F) / σ (c : F), σ (c : F) ^ 2]

omit [Finite F] [CharP F 2] in
theorem u4lPsi_mul_eq_one (c : Fˣ) : ∀ i, u4lPsiD σ c i * u4lPsiE σ c i = 1 := by
  have hc : (c : F) ≠ 0 := c.ne_zero
  have hs : σ (c : F) ≠ 0 := u4l_sigma_ne_zero σ hc
  intro i
  fin_cases i <;> simp [u4lPsiD, u4lPsiE, hc, hs] <;> field_simp

omit [Finite F] [CharP F 2] in
@[expose] noncomputable def u4lPsiFun (c : Fˣ) : GL (Fin 4) F :=
  u4lDiag (u4lPsiD σ c) (u4lPsiE σ c) (u4lPsi_mul_eq_one σ c)

omit [Finite F] [CharP F 2] in
theorem u4lPsiFun_one : u4lPsiFun σ 1 = 1 := by
  apply Units.ext
  show diagonal (u4lPsiD σ 1) = 1
  rw [← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [u4lPsiD]

omit [Finite F] [CharP F 2] in
theorem u4lPsiFun_mul (c c' : Fˣ) :
    u4lPsiFun σ (c * c') = u4lPsiFun σ c * u4lPsiFun σ c' := by
  apply Units.ext
  rw [Units.val_mul]
  show diagonal (u4lPsiD σ (c * c')) = diagonal (u4lPsiD σ c) * diagonal (u4lPsiD σ c')
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [u4lPsiD, map_mul] <;> ring

omit [Finite F] [CharP F 2] in
@[expose] noncomputable def u4lPsi : Fˣ →* GL (Fin 4) F where
  toFun := u4lPsiFun σ
  map_one' := u4lPsiFun_one σ
  map_mul' := u4lPsiFun_mul σ

omit [Finite F] [CharP F 2] in
theorem u4lPsi_val (c : Fˣ) :
    ((u4lPsi σ c : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal (u4lPsiD σ c) :=
  rfl

omit [Finite F] [CharP F 2] in
theorem u4lPsi_inv_val (c : Fˣ) :
    (((u4lPsi σ c)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal (u4lPsiE σ c) :=
  rfl

omit [Finite F] [CharP F 2] in
theorem conjTr_diagonal_eq (d : Fin 4 → F) :
    conjTr σ (diagonal d) = diagonal (fun i => σ (d i)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [conjTr]
  · simp [conjTr, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]

omit [Finite F] [CharP F 2] in
theorem u4lPsi_mem_SU (hσ : ∀ c, σ (σ c) = c) (c : Fˣ) : u4lPsi σ c ∈ SU σ 4 := by
  have hc : (c : F) ≠ 0 := c.ne_zero
  have hs : σ (c : F) ≠ 0 := u4l_sigma_ne_zero σ hc
  rw [mem_SU, u4lPsi_val]
  refine ⟨?_, ?_⟩
  · rw [det_diagonal, Fin.prod_univ_four]
    simp [u4lPsiD, hc, hs] <;> field_simp
  · rw [conjTr_diagonal_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u4lPsiD, antidiag, mul_diagonal, diagonal_mul, hσ, hc, hs] <;> field_simp

omit [Finite F] [CharP F 2] in
theorem u4lPsi_comm_iotaL (c : Fˣ) (M : SU σ 2) :
    u4lPsi σ c * iotaL σ M = iotaL σ M * u4lPsi σ c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_iotaL, u4lPsi_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u4lPsiD, blkL, mul_diagonal, diagonal_mul] <;> ring

omit [Finite F] [CharP F 2] in
theorem pattern_mul_diagonal {g : Matrix (Fin 4) (Fin 4) F} {d : Fin 4 → F}
    (h01 : g 0 1 = 0) (h02 : g 0 2 = 0) (h03 : g 0 3 = 0) (h10 : g 1 0 = 0) (h13 : g 1 3 = 0)
    (h20 : g 2 0 = 0) (h23 : g 2 3 = 0) (h30 : g 3 0 = 0) (h31 : g 3 1 = 0) (h32 : g 3 2 = 0) :
    (g * diagonal d) 0 1 = 0 ∧ (g * diagonal d) 0 2 = 0 ∧ (g * diagonal d) 0 3 = 0 ∧
      (g * diagonal d) 1 0 = 0 ∧ (g * diagonal d) 1 3 = 0 ∧ (g * diagonal d) 2 0 = 0 ∧
      (g * diagonal d) 2 3 = 0 ∧ (g * diagonal d) 3 0 = 0 ∧ (g * diagonal d) 3 1 = 0 ∧
      (g * diagonal d) 3 2 = 0 := by
  simp [mul_diagonal, h01, h02, h03, h10, h13, h20, h23, h30, h31, h32]

theorem u4l_exists_sq_eq (x : F) : ∃ c : F, c ^ 2 = x := by
  have hinj : Function.Injective (fun c : F => c ^ 2) := by
    intro a b h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
    · exact h'
    · rw [h', CharTwo.neg_eq]
  exact Finite.injective_iff_surjective.mp hinj x

theorem u4l_exists_unit_sq {x : F} (hx : x ≠ 0) : ∃ c : Fˣ, (c : F) ^ 2 = x := by
  obtain ⟨c, hc⟩ := u4l_exists_sq_eq x
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hx (by simpa using hc.symm)
  exact ⟨Units.mk0 c hc0, by simpa using hc⟩

theorem long_decomp (hσ : ∀ c, σ (σ c) = c) {t : GL (Fin 4) F} {α β γ : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, β, β, γ]) (hαβ : α ≠ β) (hαγ : α ≠ γ)
    (hβγ : β ≠ γ) :
    ∃ A : Subgroup (GL (Fin 4) F), (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) ∧
      (∀ a ∈ A, ∀ r ∈ longSL σ, a * r = r * a) ∧
      ∀ g ∈ SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F)),
        ∃ r ∈ longSL σ, ∃ a ∈ A, g = r * a := by
  refine ⟨(u4lPsi σ).range, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨c, rfl⟩ _ ⟨M, rfl⟩
    exact u4lPsi_comm_iotaL σ c M
  · rintro g ⟨hgSU, hgC⟩
    obtain ⟨h01, h02, h03, h10, h13, h20, h23, h30, h31, h32⟩ :=
      pattern_long_of_mem ht hαβ hαγ hβγ hgC
    obtain ⟨-, hiso⟩ := mem_SU.1 hgSU
    have hcorner : σ ((g : Matrix (Fin 4) (Fin 4) F) 0 0) *
        (g : Matrix (Fin 4) (Fin 4) F) 3 3 = 1 := by
      have e := congrFun (congrFun hiso 0) 3
      rw [antidiag_four] at e
      simpa [conjTr, Matrix.mul_apply, Fin.sum_univ_four, h01, h02, h03, h10, h13, h20, h23,
        h30, h31, h32] using e
    have hg00 : (g : Matrix (Fin 4) (Fin 4) F) 0 0 ≠ 0 := by
      intro h
      rw [h, map_zero, zero_mul] at hcorner
      exact zero_ne_one hcorner
    obtain ⟨c, hc⟩ := u4l_exists_unit_sq hg00
    have hr : g * (u4lPsi σ c)⁻¹ ∈ SU σ 4 :=
      mul_mem hgSU (inv_mem (u4lPsi_mem_SU σ hσ c))
    have hk : ((g * (u4lPsi σ c)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (g : Matrix (Fin 4) (Fin 4) F) * diagonal (u4lPsiE σ c) := by
      rw [Units.val_mul, u4lPsi_inv_val]
    have hkL : g * (u4lPsi σ c)⁻¹ ∈ longSL σ := by
      apply mem_longSL_of σ hr
      · rw [hk]
        exact pattern_mul_diagonal h01 h02 h03 h10 h13 h20 h23 h30 h31 h32
      · rw [hk, mul_diagonal, ← hc]
        simp [u4lPsiE, Units.ne_zero]
    exact ⟨g * (u4lPsi σ c)⁻¹, hkL, u4lPsi σ c, ⟨c, rfl⟩,
      (inv_mul_cancel_right g (u4lPsi σ c)).symm⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK423
