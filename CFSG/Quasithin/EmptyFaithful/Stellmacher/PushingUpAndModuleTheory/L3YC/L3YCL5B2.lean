module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCL5B1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.C48Pf.FMod CFSG.Quasithin.C35Pf
open scoped commutatorElement

namespace Stellmacher.PU.L3YC

@[expose] def m2 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (X : Matrix (Fin 2) (Fin 3) (ZMod 2)) :
    Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, X 0 0, X 0 1, X 0 2;
     0, 1, X 1 0, X 1 1, X 1 2;
     0, 0, A 0 0, A 0 1, A 0 2;
     0, 0, A 1 0, A 1 1, A 1 2;
     0, 0, A 2 0, A 2 1, A 2 2]

theorem m2_mul (A A' : Matrix (Fin 3) (Fin 3) (ZMod 2)) (X X' : Matrix (Fin 2) (Fin 3) (ZMod 2)) :
    m2 A X * m2 A' X' = m2 (A * A') (X * A' + X') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m2, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three, Fin.sum_univ_two] <;> ring

theorem m2_one : m2 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m2]

theorem eq_m2_of_blockForm2 {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hM : BlockForm 2 3 M) :
    ∃ X, M = m2 (blkAt 2 3 (by norm_num) M) X := by
  obtain ⟨h1, -, h3, -⟩ := hM
  refine ⟨!![M 0 2, M 0 3, M 0 4; M 1 2, M 1 3, M 1 4], ?_⟩
  have e20 : M 2 0 = 0 := h1 2 0 (by decide) (by decide)
  have e21 : M 2 1 = 0 := h1 2 1 (by decide) (by decide)
  have e30 : M 3 0 = 0 := h1 3 0 (by decide) (by decide)
  have e31 : M 3 1 = 0 := h1 3 1 (by decide) (by decide)
  have e40 : M 4 0 = 0 := h1 4 0 (by decide) (by decide)
  have e41 : M 4 1 = 0 := h1 4 1 (by decide) (by decide)
  have e00 : M 0 0 = 1 := by simpa using h3 0 0 (by decide) (by decide)
  have e01 : M 0 1 = 0 := by simpa using h3 0 1 (by decide) (by decide)
  have e10 : M 1 0 = 0 := by simpa using h3 1 0 (by decide) (by decide)
  have e11 : M 1 1 = 1 := by simpa using h3 1 1 (by decide) (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m2, blkAt_apply, *]

theorem eq_m2_of_centralizes_cross {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hdet : M.det = 1)
    (hc : ∀ k l : Fin 5, IsCross 2 3 k l →
      M * (1 + Matrix.single k l (1 : ZMod 2)) = (1 + Matrix.single k l (1 : ZMod 2)) * M) :
    ∃ Y, M = m2 1 Y := by
  have c02 := (commute_single_iff M).1 (hc 0 2 (Or.inl ⟨by decide, by decide, by decide⟩))
  have c03 := (commute_single_iff M).1 (hc 0 3 (Or.inl ⟨by decide, by decide, by decide⟩))
  have c04 := (commute_single_iff M).1 (hc 0 4 (Or.inl ⟨by decide, by decide, by decide⟩))
  have c12 := (commute_single_iff M).1 (hc 1 2 (Or.inl ⟨by decide, by decide, by decide⟩))
  obtain ⟨col0, row2, d02⟩ := c02
  obtain ⟨-, row3, d03⟩ := c03
  obtain ⟨-, row4, d04⟩ := c04
  obtain ⟨col1, -, d12⟩ := c12
  have hl : M 0 0 = 1 := by
    by_contra hne
    have h0 : M 0 0 = 0 := by
      have : ∀ t : ZMod 2, t ≠ 1 → t = 0 := by decide
      exact this _ hne
    have : M.det = 0 := Matrix.det_eq_zero_of_column_eq_zero 0 (fun i => by
      by_cases hi : i = 0
      · rw [hi]; exact h0
      · exact col0 i hi)
    rw [hdet] at this
    exact one_ne_zero this
  refine ⟨!![M 0 2, M 0 3, M 0 4; M 1 2, M 1 3, M 1 4], ?_⟩
  have a1 : M 1 1 = 1 := by rw [d12, ← d02, hl]
  have a2 : M 2 2 = 1 := by rw [← d02, hl]
  have a3 : M 3 3 = 1 := by rw [← d03, hl]
  have a4 : M 4 4 = 1 := by rw [← d04, hl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m2, hl, a1, a2, a3, a4, col0, col1, row2, row3, row4]

theorem transvection_cross_eq2 (k : Fin 2) (l : Fin 3) :
    ((1 + Matrix.single (⟨k.val, by omega⟩ : Fin 5) (⟨l.val + 2, by omega⟩ : Fin 5)
      (1 : ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2))) = m2 1 (Matrix.single k l 1) := by
  ext a b
  fin_cases k <;> fin_cases l <;> fin_cases a <;> fin_cases b <;>
    simp [m2, Matrix.single_apply]

theorem generate_V2 {B : Type} [Group B] (θ : B →* SpecialLinearGroup (Fin 5) (ZMod 2))
    (T : Subgroup B)
    (hT : ∀ (k l : Fin 5) (hc : IsCross 2 3 k l), ∃ p ∈ T,
      θ p = SpecialLinearGroup.transvection hc.ne (1 : ZMod 2))
    (Z : Matrix (Fin 2) (Fin 3) (ZMod 2)) :
    ∃ n ∈ T, ((θ n : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      m2 1 Z := by
  classical
  let P : Matrix (Fin 2) (Fin 3) (ZMod 2) → Prop := fun Z => ∃ n ∈ T,
    ((θ n : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = m2 1 Z
  have h0 : P 0 := ⟨1, T.one_mem, by
    rw [map_one, Matrix.SpecialLinearGroup.coe_one]; exact m2_one.symm⟩
  have hadd : ∀ Z Z', P Z → P Z' → P (Z + Z') := by
    rintro Z Z' ⟨n, hn, hnZ⟩ ⟨n', hn', hnZ'⟩
    refine ⟨n * n', T.mul_mem hn hn', ?_⟩
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hnZ, hnZ', m2_mul]
    simp
  have hs : ∀ (k : Fin 2) (l : Fin 3) (t : ZMod 2), P (Matrix.single k l t) := by
    intro k l t
    have ht : t = 0 ∨ t = 1 := by revert t; decide
    rcases ht with rfl | rfl
    · simpa using h0
    · have hc : IsCross 2 3 (⟨k.val, by omega⟩ : Fin 5) (⟨l.val + 2, by omega⟩ : Fin 5) :=
        Or.inl ⟨by simp; omega, by simp, by simp; omega⟩
      obtain ⟨p, hp, hpθ⟩ := hT _ _ hc
      refine ⟨p, hp, ?_⟩
      rw [hpθ, CFSG.LinearGroups.coe_transvection]
      exact transvection_cross_eq2 k l
  rw [Matrix.matrix_eq_sum_single Z]
  exact Finset.sum_induction _ P hadd h0 fun i _ =>
    Finset.sum_induction _ P hadd h0 fun j _ => hs i j (Z i j)

@[expose] def omega2_0 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0;
     1, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1]

theorem omega2_0_cube : omega2_0 * omega2_0 * omega2_0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega2_0, Matrix.mul_apply, Fin.sum_univ_five, zmod2_one_add_one]

theorem det_omega2_0 : omega2_0.det = 1 := by
  have h1 : omega2_0.det * omega2_0.det * omega2_0.det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, omega2_0_cube, Matrix.det_one]
  generalize omega2_0.det = t at h1 ⊢
  revert t
  decide

@[expose] def omega2 : SpecialLinearGroup (Fin 5) (ZMod 2) := ⟨omega2_0, det_omega2_0⟩

theorem omega2_cube : omega2 * omega2 * omega2 = 1 :=
  Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact omega2_0_cube)

theorem omega2_inv : omega2⁻¹ = omega2 * omega2 := by
  have h : omega2 * (omega2 * omega2) = 1 := by rw [← mul_assoc]; exact omega2_cube
  exact inv_eq_of_mul_eq_one_right h

theorem omega2_conj (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (X : Matrix (Fin 2) (Fin 3) (ZMod 2)) :
    omega2_0 * m2 A X * (omega2_0 * omega2_0) = m2 A (Dm * X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega2_0, m2, Dm, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two,
      zmod2_one_add_one]

theorem omega2_conj' (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (X : Matrix (Fin 2) (Fin 3) (ZMod 2)) :
    (omega2_0 * omega2_0) * m2 A X * omega2_0 = m2 A (Dm2 * X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega2_0, m2, Dm2, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two,
      zmod2_one_add_one]

section Config

variable {B : Type} [Group B]
variable (θ : B →* SpecialLinearGroup (Fin 5) (ZMod 2))
  (α : B →* SpecialLinearGroup (Fin 3) (ZMod 2))

theorem theta_shape2
    (hblk : ∀ x : B, blkAt 2 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 2 3 ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (x : B) : ∃ X, ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      m2 ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) X := by
  obtain ⟨hb1, hbf⟩ := hblk x
  obtain ⟨X, hX⟩ := eq_m2_of_blockForm2 hbf
  exact ⟨X, by rw [hX, hb1]⟩

theorem mem_theta_iff2 (hαs : Function.Surjective α)
    (hblk : ∀ x : B, blkAt 2 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 2 3 ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (hV : ∀ Z : Matrix (Fin 2) (Fin 3) (ZMod 2), ∃ n : B,
      ((θ n : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = m2 1 Z)
    (M : SpecialLinearGroup (Fin 5) (ZMod 2)) :
    M ∈ (⊤ : Subgroup B).map θ ↔ ∃ (A : SpecialLinearGroup (Fin 3) (ZMod 2))
      (X : Matrix (Fin 2) (Fin 3) (ZMod 2)),
      (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) = m2 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) X := by
  constructor
  · rintro ⟨x, -, rfl⟩
    obtain ⟨X, hX⟩ := theta_shape2 θ α hblk x
    exact ⟨α x, X, hX⟩
  · rintro ⟨A, X, hM⟩
    obtain ⟨x, hx⟩ := hαs A
    obtain ⟨Y, hY⟩ := theta_shape2 θ α hblk x
    rw [hx] at hY
    obtain ⟨n, hn⟩ := hV (X + Y)
    refine ⟨x * n, Subgroup.mem_top _, Subtype.ext ?_⟩
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hY, hn, m2_mul, hM]
    congr 1
    · exact mul_one _
    · have hYY : Y + Y = 0 := by
        ext i j
        simp [Heis.zmod2_add_self]
      rw [Matrix.mul_one, ← add_assoc, add_comm Y X, add_assoc, hYY, add_zero]

theorem m2_transvection_block (j l : Fin 5) (hj : 2 ≤ j.val) (hl : 2 ≤ l.val) (hjl : j ≠ l) :
    (1 + Matrix.single j l (1 : ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      m2 (1 + Matrix.single (⟨j.val - 2, by omega⟩ : Fin 3) (⟨l.val - 2, by omega⟩ : Fin 3) 1)
        0 := by
  have hj' : j = 2 ∨ j = 3 ∨ j = 4 := by
    fin_cases j <;> simp_all
  have hl' : l = 2 ∨ l = 3 ∨ l = 4 := by
    fin_cases l <;> simp_all
  rcases hj' with rfl | rfl | rfl <;> rcases hl' with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hjl
    | (ext a b; fin_cases a <;> fin_cases b <;> simp [m2, Matrix.single_apply])

theorem config_a2 (hθ : Function.Injective θ) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 B)
    (hblk : ∀ x : B, blkAt 2 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 2 3 ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (hcross : ∀ (k l : Fin 5) (hc : IsCross 2 3 k l), ∃ p ∈ CFSG.pCore 2 B,
      θ p = SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) :
    ∃ ω : SpecialLinearGroup (Fin 5) (ZMod 2),
      ω ∈ Subgroup.normalizer (((⊤ : Subgroup B).map θ : Subgroup (SpecialLinearGroup (Fin 5)
        (ZMod 2))) : Set (SpecialLinearGroup (Fin 5) (ZMod 2))) ∧ ω ^ 3 = 1 ∧
      (∀ (b : B) (c : SpecialLinearGroup (Fin 5) (ZMod 2)),
        (∀ n ∈ CFSG.pCore 2 B, θ n * c = c * θ n) → ω ≠ θ b * c) ∧
      ⁅CFSG.pCore 2 B, (⊤ : Subgroup B)⁆ = CFSG.pCore 2 B := by
  classical
  set N := CFSG.pCore 2 B with hN
  have hV : ∀ Z : Matrix (Fin 2) (Fin 3) (ZMod 2), ∃ n : B,
      ((θ n : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = m2 1 Z :=
    fun Z => by
      obtain ⟨n, -, hn⟩ := generate_V2 θ N hcross Z
      exact ⟨n, hn⟩
  have hmem := mem_theta_iff2 θ α hαs hblk hV
  have key : ∀ M ∈ (⊤ : Subgroup B).map θ, omega2 * M * omega2⁻¹ ∈ (⊤ : Subgroup B).map θ ∧
      omega2⁻¹ * M * omega2 ∈ (⊤ : Subgroup B).map θ := by
    intro M hM
    obtain ⟨A, X, hMA⟩ := (hmem M).1 hM
    constructor
    · refine (hmem _).2 ⟨A, Dm * X, ?_⟩
      rw [omega2_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, hMA]
      exact omega2_conj _ _
    · refine (hmem _).2 ⟨A, Dm2 * X, ?_⟩
      rw [omega2_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, hMA]
      exact omega2_conj' _ _
  refine ⟨omega2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro M
    constructor
    · intro hM
      exact (key M hM).1
    · intro hM
      have := (key _ hM).2
      have e : omega2⁻¹ * (omega2 * M * omega2⁻¹) * omega2 = M := by group
      rwa [e] at this
  · calc omega2 ^ 3 = omega2 * omega2 * omega2 := by rw [pow_three, mul_assoc]
      _ = 1 := omega2_cube
  · intro b c hc hω
    have hcc : ∀ k l : Fin 5, IsCross 2 3 k l →
        (c : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (1 + Matrix.single k l (1 : ZMod 2)) =
          (1 + Matrix.single k l (1 : ZMod 2)) * (c : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
      intro k l hkl
      obtain ⟨p, hp, hpθ⟩ := hcross k l hkl
      have := hc p hp
      rw [hpθ] at this
      have h2 := congrArg (fun g : SpecialLinearGroup (Fin 5) (ZMod 2) =>
        (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) this
      simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection] at h2
      exact h2.symm
    obtain ⟨Y, hY⟩ := eq_m2_of_centralizes_cross c.2 hcc
    obtain ⟨Y₀, hY₀⟩ := theta_shape2 θ α hblk b
    have h3 := congrArg (fun g : SpecialLinearGroup (Fin 5) (ZMod 2) =>
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) hω
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h3
    rw [hY₀, hY, m2_mul] at h3
    have h4 := congrFun (congrFun h3 0) 0
    simp [omega2, omega2_0, m2] at h4
  · refine le_antisymm (Subgroup.commutator_le_left N ⊤) ?_
    set C := ⁅N, (⊤ : Subgroup B)⁆ with hC
    have hcrossC : ∀ (k l : Fin 5) (hc : IsCross 2 3 k l), ∃ p ∈ C,
        θ p = SpecialLinearGroup.transvection hc.ne (1 : ZMod 2) := by
      intro k l hc
      have hk : k.val < 2 := by rcases hc with h | h <;> omega
      have hl : 2 ≤ l.val := by rcases hc with h | h <;> omega
      obtain ⟨j, hj2, hjl⟩ : ∃ j : Fin 5, 2 ≤ j.val ∧ j ≠ l := by
        by_cases h0 : l.val = 2
        · exact ⟨⟨3, by omega⟩, by simp, fun h => by
            have := congrArg Fin.val h
            simp at this
            omega⟩
        · exact ⟨⟨2, by omega⟩, by simp, fun h => by
            have := congrArg Fin.val h
            simp at this
            omega⟩
      have hkj : k ≠ j := fun h => by
        have := congrArg Fin.val h
        omega
      have hcj : IsCross 2 3 k j := Or.inl ⟨by omega, hj2, by omega⟩
      obtain ⟨p, hp, hpθ⟩ := hcross k j hcj
      have hMeq := m2_transvection_block j l hj2 hl hjl
      have hMS : (SpecialLinearGroup.transvection hjl (1 : ZMod 2)) ∈
          (⊤ : Subgroup B).map θ := by
        refine (hmem _).2 ⟨SpecialLinearGroup.transvection
          (fun h => hjl (Fin.ext (by
            have := congrArg Fin.val h
            simp at this
            omega)) :
            (⟨j.val - 2, by omega⟩ : Fin 3) ≠ ⟨l.val - 2, by omega⟩) (1 : ZMod 2), 0, ?_⟩
        rw [CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection]
        exact hMeq
      obtain ⟨b, -, hb⟩ := hMS
      refine ⟨⁅p, b⁆, ?_, ?_⟩
      · rw [hC]
        exact Subgroup.commutator_mem_commutator hp (Subgroup.mem_top b)
      · rw [map_commutatorElement, hb, hpθ,
          SpecialLinearGroup.commutatorElement_transvection hkj hjl hc.ne, mul_one]
    intro n₀ hn₀
    have hα1 : α n₀ = 1 := by
      rw [← MonoidHom.mem_ker, hαk]
      exact hn₀
    obtain ⟨X, hX⟩ := theta_shape2 θ α hblk n₀
    rw [hα1, Matrix.SpecialLinearGroup.coe_one] at hX
    obtain ⟨n', hn'C, hn'⟩ := generate_V2 θ C hcrossC X
    have h1 : θ n₀ = θ n' := Subtype.ext (by rw [hX, hn'])
    have := hθ h1
    rw [this]
    exact hn'C

end Config

end Stellmacher.PU.L3YC

end CFSG.Quasithin
