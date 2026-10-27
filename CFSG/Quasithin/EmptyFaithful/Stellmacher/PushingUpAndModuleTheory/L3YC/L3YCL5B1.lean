module

public import CFSG.Quasithin.Background.C35InspL45A
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCHeis
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.C48Pf.FMod CFSG.Quasithin.C35Pf
open scoped commutatorElement

namespace Stellmacher.PU.L3YC

@[expose] def m1 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (X : Matrix (Fin 3) (Fin 2) (ZMod 2)) :
    Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![A 0 0, A 0 1, A 0 2, X 0 0, X 0 1;
     A 1 0, A 1 1, A 1 2, X 1 0, X 1 1;
     A 2 0, A 2 1, A 2 2, X 2 0, X 2 1;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1]

theorem m1_mul (A A' : Matrix (Fin 3) (Fin 3) (ZMod 2)) (X X' : Matrix (Fin 3) (Fin 2) (ZMod 2)) :
    m1 A X * m1 A' X' = m1 (A * A') (A * X' + X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m1, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three]

theorem m1_one : m1 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m1]

theorem blkAt_m1 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (X : Matrix (Fin 3) (Fin 2) (ZMod 2)) :
    blkAt 0 3 (by norm_num) (m1 A X) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkAt_apply, m1]

theorem eq_m1_of_blockForm0 {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hM : BlockForm 0 3 M) :
    ∃ X, M = m1 (blkAt 0 3 (by norm_num) M) X := by
  obtain ⟨-, h2, -, h4⟩ := hM
  refine ⟨!![M 0 3, M 0 4; M 1 3, M 1 4; M 2 3, M 2 4], ?_⟩
  have e30 : M 3 0 = 0 := h2 3 0 (by decide) (by decide)
  have e31 : M 3 1 = 0 := h2 3 1 (by decide) (by decide)
  have e32 : M 3 2 = 0 := h2 3 2 (by decide) (by decide)
  have e40 : M 4 0 = 0 := h2 4 0 (by decide) (by decide)
  have e41 : M 4 1 = 0 := h2 4 1 (by decide) (by decide)
  have e42 : M 4 2 = 0 := h2 4 2 (by decide) (by decide)
  have e33 : M 3 3 = 1 := by simpa using h4 3 3 (by decide) (by decide)
  have e34 : M 3 4 = 0 := by simpa using h4 3 4 (by decide) (by decide)
  have e43 : M 4 3 = 0 := by simpa using h4 4 3 (by decide) (by decide)
  have e44 : M 4 4 = 1 := by simpa using h4 4 4 (by decide) (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m1, blkAt_apply, *]

theorem eq_m1_of_centralizes_cross {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hdet : M.det = 1)
    (hc : ∀ k l : Fin 5, IsCross 0 3 k l →
      M * (1 + Matrix.single k l (1 : ZMod 2)) = (1 + Matrix.single k l (1 : ZMod 2)) * M) :
    ∃ Y, M = m1 1 Y := by
  have c03 := (commute_single_iff M).1 (hc 0 3 (Or.inr ⟨by decide, by decide, by decide⟩))
  have c04 := (commute_single_iff M).1 (hc 0 4 (Or.inr ⟨by decide, by decide, by decide⟩))
  have c13 := (commute_single_iff M).1 (hc 1 3 (Or.inr ⟨by decide, by decide, by decide⟩))
  have c23 := (commute_single_iff M).1 (hc 2 3 (Or.inr ⟨by decide, by decide, by decide⟩))
  obtain ⟨col0, row3, d03⟩ := c03
  obtain ⟨-, row4, d04⟩ := c04
  obtain ⟨col1, -, d13⟩ := c13
  obtain ⟨col2, -, d23⟩ := c23
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
  refine ⟨!![M 0 3, M 0 4; M 1 3, M 1 4; M 2 3, M 2 4], ?_⟩
  have a1 : M 1 1 = 1 := by rw [d13, ← d03, hl]
  have a2 : M 2 2 = 1 := by rw [d23, ← d03, hl]
  have a3 : M 3 3 = 1 := by rw [← d03, hl]
  have a4 : M 4 4 = 1 := by rw [← d04, hl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m1, hl, a1, a2, a3, a4, col0, col1, col2, row3, row4]

theorem transvection_cross_eq (k : Fin 3) (l : Fin 2) :
    ((1 + Matrix.single (⟨k.val, by omega⟩ : Fin 5) (⟨l.val + 3, by omega⟩ : Fin 5)
      (1 : ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2))) = m1 1 (Matrix.single k l 1) := by
  ext a b
  fin_cases k <;> fin_cases l <;> fin_cases a <;> fin_cases b <;>
    simp [m1, Matrix.single_apply]

theorem generate_V1 {B : Type} [Group B] (θ : B →* SpecialLinearGroup (Fin 5) (ZMod 2))
    (T : Subgroup B)
    (hT : ∀ (k l : Fin 5) (hc : IsCross 0 3 k l), ∃ p ∈ T,
      θ p = SpecialLinearGroup.transvection hc.ne (1 : ZMod 2))
    (Z : Matrix (Fin 3) (Fin 2) (ZMod 2)) :
    ∃ n ∈ T, ((θ n : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      m1 1 Z := by
  classical
  let P : Matrix (Fin 3) (Fin 2) (ZMod 2) → Prop := fun Z => ∃ n ∈ T,
    ((θ n : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = m1 1 Z
  have h0 : P 0 := ⟨1, T.one_mem, by rw [map_one, Matrix.SpecialLinearGroup.coe_one]; exact m1_one.symm⟩
  have hadd : ∀ Z Z', P Z → P Z' → P (Z + Z') := by
    rintro Z Z' ⟨n, hn, hnZ⟩ ⟨n', hn', hnZ'⟩
    refine ⟨n * n', T.mul_mem hn hn', ?_⟩
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hnZ, hnZ', m1_mul]
    simp [add_comm]
  have hs : ∀ (k : Fin 3) (l : Fin 2) (t : ZMod 2), P (Matrix.single k l t) := by
    intro k l t
    have ht : t = 0 ∨ t = 1 := by revert t; decide
    rcases ht with rfl | rfl
    · simpa using h0
    · have hc : IsCross 0 3 (⟨k.val, by omega⟩ : Fin 5) (⟨l.val + 3, by omega⟩ : Fin 5) :=
        Or.inr ⟨by simp, by simp, by simp⟩
      obtain ⟨p, hp, hpθ⟩ := hT _ _ hc
      refine ⟨p, hp, ?_⟩
      rw [hpθ, CFSG.LinearGroups.coe_transvection]
      exact transvection_cross_eq k l
  rw [Matrix.matrix_eq_sum_single Z]
  exact Finset.sum_induction _ P hadd h0 fun i _ =>
    Finset.sum_induction _ P hadd h0 fun j _ => hs i j (Z i j)

@[expose] def omega0 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 0, 1;
     0, 0, 0, 1, 1]

theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

theorem omega0_cube : omega0 * omega0 * omega0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega0, Matrix.mul_apply, Fin.sum_univ_five, zmod2_one_add_one]

@[expose] def Dm : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]
@[expose] def Dm2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 1, 0]

theorem det_omega0 : omega0.det = 1 := by
  have h1 : omega0.det * omega0.det * omega0.det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, omega0_cube, Matrix.det_one]
  generalize omega0.det = t at h1 ⊢
  revert t
  decide

@[expose] def omega : SpecialLinearGroup (Fin 5) (ZMod 2) := ⟨omega0, det_omega0⟩

theorem omega_cube : omega * omega * omega = 1 :=
  Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact omega0_cube)

theorem omega_inv : omega⁻¹ = omega * omega := by
  have h : omega * (omega * omega) = 1 := by rw [← mul_assoc]; exact omega_cube
  exact inv_eq_of_mul_eq_one_right h

theorem omega_conj (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (X : Matrix (Fin 3) (Fin 2) (ZMod 2)) :
    omega0 * m1 A X * (omega0 * omega0) = m1 A (X * Dm2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega0, m1, Dm, Dm2, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two,
      zmod2_one_add_one]

theorem omega_conj' (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (X : Matrix (Fin 3) (Fin 2) (ZMod 2)) :
    (omega0 * omega0) * m1 A X * omega0 = m1 A (X * Dm) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega0, m1, Dm, Dm2, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two,
      zmod2_one_add_one]

section Config

variable {B : Type} [Group B]
variable (θ : B →* SpecialLinearGroup (Fin 5) (ZMod 2))
  (α : B →* SpecialLinearGroup (Fin 3) (ZMod 2))

theorem theta_shape
    (hblk : ∀ x : B, blkAt 0 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 0 3 ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (x : B) : ∃ X, ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      m1 ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) X := by
  obtain ⟨hb1, hbf⟩ := hblk x
  obtain ⟨X, hX⟩ := eq_m1_of_blockForm0 hbf
  exact ⟨X, by rw [hX, hb1]⟩

theorem mem_theta_iff (hαs : Function.Surjective α)
    (hblk : ∀ x : B, blkAt 0 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 0 3 ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (hV : ∀ Z : Matrix (Fin 3) (Fin 2) (ZMod 2), ∃ n : B,
      ((θ n : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = m1 1 Z)
    (M : SpecialLinearGroup (Fin 5) (ZMod 2)) :
    M ∈ (⊤ : Subgroup B).map θ ↔ ∃ (A : SpecialLinearGroup (Fin 3) (ZMod 2))
      (X : Matrix (Fin 3) (Fin 2) (ZMod 2)),
      (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) = m1 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) X := by
  constructor
  · rintro ⟨x, -, rfl⟩
    obtain ⟨X, hX⟩ := theta_shape θ α hblk x
    exact ⟨α x, X, hX⟩
  · rintro ⟨A, X, hM⟩
    obtain ⟨x, hx⟩ := hαs A
    obtain ⟨Y, hY⟩ := theta_shape θ α hblk x
    rw [hx] at hY
    obtain ⟨n, hn⟩ := hV (((A⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) * (X + Y))
    refine ⟨x * n, Subgroup.mem_top _, Subtype.ext ?_⟩
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hY, hn, m1_mul, hM]
    congr 1
    · exact mul_one _
    · have : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * ((A⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
      have hYY : Y + Y = 0 := by
        ext i j
        simp [Heis.zmod2_add_self]
      rw [← Matrix.mul_assoc, this, Matrix.one_mul, add_assoc, hYY, add_zero]

theorem m1_transvection_block (k j : Fin 3) (hkj : k ≠ j) :
    (1 + Matrix.single (⟨k.val, by omega⟩ : Fin 5) (⟨j.val, by omega⟩ : Fin 5) (1 : ZMod 2) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) = m1 (1 + Matrix.single k j 1) 0 := by
  ext a b
  fin_cases k <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [m1, Matrix.single_apply] <;> exact absurd rfl hkj

theorem config_a0 (hθ : Function.Injective θ) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 B)
    (hblk : ∀ x : B, blkAt 0 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 0 3 ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (hcross : ∀ (k l : Fin 5) (hc : IsCross 0 3 k l), ∃ p ∈ CFSG.pCore 2 B,
      θ p = SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) :
    ∃ ω : SpecialLinearGroup (Fin 5) (ZMod 2),
      ω ∈ Subgroup.normalizer (((⊤ : Subgroup B).map θ : Subgroup (SpecialLinearGroup (Fin 5)
        (ZMod 2))) : Set (SpecialLinearGroup (Fin 5) (ZMod 2))) ∧ ω ^ 3 = 1 ∧
      (∀ (b : B) (c : SpecialLinearGroup (Fin 5) (ZMod 2)),
        (∀ n ∈ CFSG.pCore 2 B, θ n * c = c * θ n) → ω ≠ θ b * c) ∧
      ⁅CFSG.pCore 2 B, (⊤ : Subgroup B)⁆ = CFSG.pCore 2 B := by
  classical
  set N := CFSG.pCore 2 B with hN
  have hV : ∀ Z : Matrix (Fin 3) (Fin 2) (ZMod 2), ∃ n : B,
      ((θ n : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = m1 1 Z :=
    fun Z => by
      obtain ⟨n, -, hn⟩ := generate_V1 θ N hcross Z
      exact ⟨n, hn⟩
  have hmem := mem_theta_iff θ α hαs hblk hV
  have key : ∀ M ∈ (⊤ : Subgroup B).map θ, omega * M * omega⁻¹ ∈ (⊤ : Subgroup B).map θ ∧
      omega⁻¹ * M * omega ∈ (⊤ : Subgroup B).map θ := by
    intro M hM
    obtain ⟨A, X, hMA⟩ := (hmem M).1 hM
    constructor
    · refine (hmem _).2 ⟨A, X * Dm2, ?_⟩
      rw [omega_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, hMA]
      exact omega_conj _ _
    · refine (hmem _).2 ⟨A, X * Dm, ?_⟩
      rw [omega_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, hMA]
      exact omega_conj' _ _
  refine ⟨omega, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro M
    constructor
    · intro hM
      exact (key M hM).1
    · intro hM
      have := (key _ hM).2
      have e : omega⁻¹ * (omega * M * omega⁻¹) * omega = M := by group
      rwa [e] at this
  · calc omega ^ 3 = omega * omega * omega := by rw [pow_three, mul_assoc]
      _ = 1 := omega_cube
  · intro b c hc hω
    have hcc : ∀ k l : Fin 5, IsCross 0 3 k l →
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
    obtain ⟨Y, hY⟩ := eq_m1_of_centralizes_cross c.2 hcc
    obtain ⟨Y₀, hY₀⟩ := theta_shape θ α hblk b
    have h3 := congrArg (fun g : SpecialLinearGroup (Fin 5) (ZMod 2) =>
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) hω
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h3
    rw [hY₀, hY, m1_mul] at h3
    have h4 := congrFun (congrFun h3 3) 3
    simp [omega, omega0, m1] at h4
  · refine le_antisymm (Subgroup.commutator_le_left N ⊤) ?_
    set C := ⁅N, (⊤ : Subgroup B)⁆ with hC
    have hcrossC : ∀ (k l : Fin 5) (hc : IsCross 0 3 k l), ∃ p ∈ C,
        θ p = SpecialLinearGroup.transvection hc.ne (1 : ZMod 2) := by
      intro k l hc
      have hk : k.val < 3 := by rcases hc with h | h <;> omega
      have hl : 3 ≤ l.val := by rcases hc with h | h <;> omega
      obtain ⟨j, hj3, hjk⟩ : ∃ j : Fin 5, j.val < 3 ∧ j ≠ k := by
        by_cases h0 : k.val = 0
        · exact ⟨⟨1, by omega⟩, by simp, fun h => by
            have := congrArg Fin.val h
            simp at this
            omega⟩
        · exact ⟨⟨0, by omega⟩, by simp, fun h => by
            have := congrArg Fin.val h
            simp at this
            omega⟩
      have hjl : j ≠ l := fun h => by
        have := congrArg Fin.val h
        omega
      have hcjl : IsCross 0 3 j l := Or.inr ⟨by omega, hj3, hl⟩
      obtain ⟨p, hp, hpθ⟩ := hcross j l hcjl
      have hkj : k ≠ j := hjk.symm
      have hk3 : k.val < 3 := hk
      have hMeq := m1_transvection_block (⟨k.val, hk⟩ : Fin 3) (⟨j.val, hj3⟩ : Fin 3)
        (fun h => hkj (Fin.ext (by simpa using congrArg Fin.val h)))
      have hMS : (SpecialLinearGroup.transvection hkj (1 : ZMod 2)) ∈ (⊤ : Subgroup B).map θ := by
        refine (hmem _).2 ⟨SpecialLinearGroup.transvection
          (fun h => hkj (Fin.ext (by simpa using congrArg Fin.val h)) :
            (⟨k.val, hk⟩ : Fin 3) ≠ ⟨j.val, hj3⟩) (1 : ZMod 2), 0, ?_⟩
        rw [CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection]
        exact hMeq
      obtain ⟨b, -, hb⟩ := hMS
      refine ⟨⁅b, p⁆, ?_, ?_⟩
      · rw [hC, ← Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top b) hp
      · rw [map_commutatorElement, hb, hpθ,
          SpecialLinearGroup.commutatorElement_transvection hkj hjl hc.ne, mul_one]
    intro n₀ hn₀
    have hα1 : α n₀ = 1 := by
      rw [← MonoidHom.mem_ker, hαk]
      exact hn₀
    obtain ⟨X, hX⟩ := theta_shape θ α hblk n₀
    rw [hα1, Matrix.SpecialLinearGroup.coe_one] at hX
    obtain ⟨n', hn'C, hn'⟩ := generate_V1 θ C hcrossC X
    have h1 : θ n₀ = θ n' := Subtype.ext (by rw [hX, hn'])
    have := hθ h1
    rw [this]
    exact hn'C

end Config

end Stellmacher.PU.L3YC

end CFSG.Quasithin
