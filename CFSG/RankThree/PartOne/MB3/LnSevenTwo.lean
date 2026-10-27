module

public import CFSG.RankThree.PartOne.MB3.LnSevenMat
public import CFSG.RankThree.PartOne.MB3.CompSimple

public section

namespace CFSG.RankThree.PartOne.MB3

open Matrix Subgroup
open scoped commutatorElement

variable {κ : Type} [Fintype κ] [DecidableEq κ]

@[expose] def bd2 (P Q R S : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2) :=
  fromBlocks (fromBlocks P Q R S) 0 0 1

theorem bd2_mul (P Q R S P' Q' R' S' : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (bd2 P Q R S : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) *
        bd2 P' Q' R' S' =
      bd2 (P * P' + Q * R') (P * Q' + Q * S') (R * P' + S * R') (R * Q' + S * S') := by
  simp [bd2, fromBlocks_multiply]

theorem bd2_det (P Q R S : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (bd2 P Q R S : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)).det =
      (fromBlocks P Q R S).det := by
  rw [bd2, det_fromBlocks_zero₂₁, det_one, mul_one]

omit [Fintype κ] in
theorem bd2_inj {P Q R S P' Q' R' S' : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : (bd2 P Q R S : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) =
      bd2 P' Q' R' S') : P = P' ∧ Q = Q' ∧ R = R' ∧ S = S' := by
  simpa [bd2, fromBlocks_inj] using h

theorem exists_bd2_of_commute {D₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hD₁ : ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M * (D₁ - 1) = 1 ∧ (D₁ - 1) * M = 1)
    (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1)
    {A : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)} (hdet : A.det = 1)
    (h : A * bd2 cM 0 0 D₁ = bd2 cM 0 0 D₁ * A) :
    ∃ P Q R S : Matrix (Fin 3) (Fin 3) (ZMod 2), A = bd2 P Q R S ∧ P * cM = cM * P ∧
      Q * D₁ = cM * Q ∧ R * cM = D₁ * R ∧ S * D₁ = D₁ * S ∧
      (fromBlocks P Q R S).det = 1 := by
  obtain ⟨A₁₁, A₁₂, A₂₁, A₂₂, rfl⟩ : ∃ (A₁₁ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
      (A₁₂ : Matrix (Fin 3 ⊕ Fin 3) κ (ZMod 2)) (A₂₁ : Matrix κ (Fin 3 ⊕ Fin 3) (ZMod 2))
      (A₂₂ : Matrix κ κ (ZMod 2)), A = fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ :=
    ⟨_, _, _, _, (fromBlocks_toBlocks A).symm⟩
  obtain ⟨M₁, hM₁, hM₁'⟩ := hD₁
  obtain ⟨M₀, hM₀, hM₀'⟩ := exists_inv_cM_sub_one
  have hl : ∃ N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2),
      N * (fromBlocks cM 0 0 D₁ - 1) = 1 := ⟨_, fromBlocks_sub_one_inv hM₀ hM₁⟩
  have hr : ∃ N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2),
      (fromBlocks cM 0 0 D₁ - 1) * N = 1 := ⟨_, fromBlocks_sub_one_inv' hM₀' hM₁'⟩
  simp only [bd2, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul, fromBlocks_inj] at h
  obtain ⟨h11, h12, h21, -⟩ := h
  have h12' : A₁₂ = 0 := eq_zero_of_mul_eq_self hl h12.symm
  have h21' : A₂₁ = 0 := eq_zero_of_mul_eq_self' hr h21
  subst h12' h21'
  rw [det_fromBlocks_zero₂₁] at hdet
  have key : ∀ a b : ZMod 2, a * b = 1 → a = 1 ∧ b = 1 := by decide
  obtain ⟨hd11, hd22⟩ := key _ _ hdet
  have hA22 : A₂₂ = 1 := hκ A₂₂ hd22
  subst hA22
  obtain ⟨P, Q, R, S, rfl⟩ : ∃ (P Q R S : Matrix (Fin 3) (Fin 3) (ZMod 2)),
      A₁₁ = fromBlocks P Q R S := by
    obtain ⟨P, Q, R, S, e⟩ : ∃ (P : Matrix (Fin 3) (Fin 3) (ZMod 2))
        (Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) (R : Matrix (Fin 3) (Fin 3) (ZMod 2))
        (S : Matrix (Fin 3) (Fin 3) (ZMod 2)), A₁₁ = fromBlocks P Q R S :=
      ⟨_, _, _, _, (fromBlocks_toBlocks A₁₁).symm⟩
    exact ⟨P, Q, R, S, e⟩
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    fromBlocks_inj] at h11
  obtain ⟨hP, hQ, hR, hS⟩ := h11
  exact ⟨P, Q, R, S, rfl, hP, hQ, hR, hS, hd11⟩

section Three

variable (κ) in
@[expose] def β₃ : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2) :=
  ⟨bd2 cM 0 0 (cM ^ 3), by
    rw [bd2_det, det_fromBlocks_zero₂₁, det_pow, cM_det]
    simp⟩

theorem coe_β₃ : ((β₃ κ : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) :
    Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) = bd2 cM 0 0 (cM ^ 3) := rfl

@[expose] def T₃ : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) :=
  Subgroup.centralizer {(β₃ κ : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))}

theorem mem_T₃ {A : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)} :
    A ∈ (T₃ : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))) ↔
      A * β₃ κ = β₃ κ * A := by
  rw [T₃, Subgroup.mem_centralizer_singleton_iff]

theorem exists_pow_of_commute_β₃ (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1)
    {A : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)} (h : A * β₃ κ = β₃ κ * A) :
    ∃ i j : ℕ, (A : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) =
      bd2 (cM ^ i) 0 0 (cM ^ j) := by
  have hA := congrArg Subtype.val h
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_β₃] at hA
  obtain ⟨P, Q, R, S, hPQRS, hP, hQ, hR, hS, hdet⟩ :=
    exists_bd2_of_commute exists_inv_cM_pow_three_sub_one hκ A.2 hA
  have hQ0 : Q = 0 := intertwine_zero Q hQ
  have hR0 : R = 0 := intertwine_zero' R hR
  subst hQ0 hR0
  rw [det_fromBlocks_zero₂₁] at hdet
  have key : ∀ a b : ZMod 2, a * b = 1 → a = 1 ∧ b = 1 := by decide
  obtain ⟨hdP, hdS⟩ := key _ _ hdet
  have hne : ∀ U : Matrix (Fin 3) (Fin 3) (ZMod 2), U.det = 1 → U ≠ 0 := by
    rintro U hU rfl
    rw [Matrix.det_zero] at hU
    exact zero_ne_one hU
  rcases comm_cM P hP with h0 | ⟨i, hi⟩
  · exact absurd h0 (hne P hdP)
  rcases comm_cM S (commute_cM_of_commute_cM_pow_three S hS) with h0 | ⟨j, hj⟩
  · exact absurd h0 (hne S hdS)
  exact ⟨i, j, by rw [hPQRS, hi, hj]⟩

theorem mul_comm_of_mem_T₃ (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1)
    (x y : ↥(T₃ : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)))) :
    x * y = y * x := by
  obtain ⟨i, j, hx⟩ := exists_pow_of_commute_β₃ hκ (mem_T₃.mp x.2)
  obtain ⟨k, l, hy⟩ := exists_pow_of_commute_β₃ hκ (mem_T₃.mp y.2)
  apply Subtype.ext
  apply Subtype.ext
  show (x : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)).1 * (y : SpecialLinearGroup _ _).1 =
    (y : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)).1 * (x : SpecialLinearGroup _ _).1
  rw [hx, hy, bd2_mul, bd2_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [(Commute.pow_pow_self cM i k).eq, (Commute.pow_pow_self cM j l).eq]

theorem not_isComponent_T₃ (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1)
    {E : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))} :
    ¬ CFSG.IsComponent (E.subgroupOf T₃) :=
  not_isComponent_of_commute (mul_comm_of_mem_T₃ hκ)

end Three

end CFSG.RankThree.PartOne.MB3
