module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3Plus
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3Minus
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char
import CFSG.Quasithin.EmptyFaithful.E22SFrame
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace Item211Lie2Proof

section Linear

open LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def sZero : SL(3, K) :=
  ⟨Matrix.diagonal ![-1, -1, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

theorem coe_sZero :
    ((sZero : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![-1, -1, 1] :=
  rfl

@[expose] def blockMat (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem det_blockMat (A : Matrix (Fin 2) (Fin 2) K) : (blockMat A).det = A.det := by
  simp [blockMat, Matrix.det_fin_three, Matrix.det_fin_two]

theorem blockMat_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    blockMat (A * B) = blockMat A * blockMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockMat_one : blockMat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

@[expose] def blockEmb : SL(2, K) →* SL(3, K) where
  toFun A := ⟨blockMat A, by rw [det_blockMat, A.2]⟩
  map_one' := Subtype.ext blockMat_one
  map_mul' A B := Subtype.ext (blockMat_mul _ _)

theorem coe_blockEmb (A : SL(2, K)) :
    ((blockEmb A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = blockMat A :=
  rfl

@[expose] def IsBlock (M : Matrix (Fin 3) (Fin 3) K) : Prop :=
  M 0 2 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

@[expose] def IsBlockScalar (M : Matrix (Fin 3) (Fin 3) K) : Prop :=
  IsBlock M ∧ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1

theorem isBlock_of_commute (hK2 : (2 : K) ≠ 0) {M : Matrix (Fin 3) (Fin 3) K}
    (h : M * ((sZero : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      ((sZero : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * M) : IsBlock M := by
  rw [coe_sZero] at h
  have hne : (-1 : K) ≠ 1 := by
    intro h1
    apply hK2
    linear_combination -h1
  refine ⟨Sec4.entry_eq_zero_of_commute_diagonal h ?_,
    Sec4.entry_eq_zero_of_commute_diagonal h ?_, Sec4.entry_eq_zero_of_commute_diagonal h ?_,
    Sec4.entry_eq_zero_of_commute_diagonal h ?_⟩ <;> simp [hne, hne.symm]

theorem commute_sZero_of_isBlock {M : Matrix (Fin 3) (Fin 3) K} (hM : IsBlock M) :
    M * ((sZero : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      ((sZero : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * M := by
  obtain ⟨h02, h12, h20, h21⟩ := hM
  rw [coe_sZero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, h02, h12, h20, h21]

theorem isBlock_blockMat (A : Matrix (Fin 2) (Fin 2) K) : IsBlock (blockMat A) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [blockMat]

theorem mul_apply_two_two {M N : Matrix (Fin 3) (Fin 3) K} (hM : IsBlock M) (hN : IsBlock N) :
    (M * N) 2 2 = M 2 2 * N 2 2 := by
  obtain ⟨-, -, hM20, hM21⟩ := hM
  obtain ⟨hN02, hN12, -, -⟩ := hN
  simp [Matrix.mul_apply, Fin.sum_univ_three, hM20, hM21, hN02, hN12]

theorem det_of_isBlock {M : Matrix (Fin 3) (Fin 3) K} (hM : IsBlock M) :
    M.det = (M 0 0 * M 1 1 - M 0 1 * M 1 0) * M 2 2 := by
  obtain ⟨h02, h12, h20, h21⟩ := hM
  rw [Matrix.det_fin_three, h02, h12, h20, h21]
  ring

theorem commute_blockMat_of_isBlockScalar {M : Matrix (Fin 3) (Fin 3) K} (hM : IsBlockScalar M)
    (A : Matrix (Fin 2) (Fin 2) K) : M * blockMat A = blockMat A * M := by
  obtain ⟨⟨h02, h12, h20, h21⟩, h01, h10, h00⟩ := hM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h20, h21, h01, h10, h00] <;>
    ring1

theorem isBlockScalar_of_commute_transvections {M : Matrix (Fin 3) (Fin 3) K} (hM : IsBlock M)
    (hu : M * blockMat !![1, 1; 0, 1] = blockMat !![1, 1; 0, 1] * M)
    (hl : M * blockMat !![1, 0; 1, 1] = blockMat !![1, 0; 1, 1] * M) : IsBlockScalar M := by
  have e1 := congrFun (congrFun hu 0) 0
  have e2 := congrFun (congrFun hu 0) 1
  have e3 := congrFun (congrFun hl 1) 1
  simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three] at e1 e2 e3
  refine ⟨hM, ?_, ?_, ?_⟩
  · linear_combination e3
  · linear_combination e1
  · linear_combination e2

theorem commute_of_commute_of_not_blockScalar {M N N' : Matrix (Fin 3) (Fin 3) K}
    (hM : IsBlock M) (hN : IsBlock N) (hN' : IsBlock N') (hMs : ¬ IsBlockScalar M)
    (hMN : M * N = N * M) (hMN' : M * N' = N' * M) : N * N' = N' * N := by
  obtain ⟨hM02, hM12, hM20, hM21⟩ := hM
  obtain ⟨hN02, hN12, hN20, hN21⟩ := hN
  obtain ⟨hN'02, hN'12, hN'20, hN'21⟩ := hN'
  have a1 := congrFun (congrFun hMN 0) 0
  have a2 := congrFun (congrFun hMN 0) 1
  have a3 := congrFun (congrFun hMN 1) 0
  have b1 := congrFun (congrFun hMN' 0) 0
  have b2 := congrFun (congrFun hMN' 0) 1
  have b3 := congrFun (congrFun hMN' 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, hM02, hM12, hM20, hM21, hN02, hN12, hN20,
    hN21, hN'02, hN'12, hN'20, hN'21, mul_zero, add_zero] at a1 a2 a3 b1 b2 b3
  have key : N 0 1 * N' 1 0 = N' 0 1 * N 1 0 ∧
      N' 0 1 * (N 0 0 - N 1 1) = N 0 1 * (N' 0 0 - N' 1 1) ∧
      N 1 0 * (N' 0 0 - N' 1 1) = N' 1 0 * (N 0 0 - N 1 1) := by
    by_cases ha : M 0 1 = 0
    · by_cases hb : M 1 0 = 0
      · have hc : M 0 0 - M 1 1 ≠ 0 := by
          intro hc
          exact hMs ⟨⟨hM02, hM12, hM20, hM21⟩, ha, hb, sub_eq_zero.mp hc⟩
        have hx : N 0 1 = 0 := by
          have : N 0 1 * (M 0 0 - M 1 1) = 0 := by
            rw [ha] at a2; linear_combination a2
          exact (mul_eq_zero.mp this).resolve_right hc
        have hy : N 1 0 = 0 := by
          have : N 1 0 * (M 0 0 - M 1 1) = 0 := by
            rw [hb] at a3; linear_combination -a3
          exact (mul_eq_zero.mp this).resolve_right hc
        have hx' : N' 0 1 = 0 := by
          have : N' 0 1 * (M 0 0 - M 1 1) = 0 := by
            rw [ha] at b2; linear_combination b2
          exact (mul_eq_zero.mp this).resolve_right hc
        have hy' : N' 1 0 = 0 := by
          have : N' 1 0 * (M 0 0 - M 1 1) = 0 := by
            rw [hb] at b3; linear_combination -b3
          exact (mul_eq_zero.mp this).resolve_right hc
        refine ⟨?_, ?_, ?_⟩ <;> simp [hx, hy, hx', hy']
      · have t1 : N 0 1 * N' 1 0 = N' 0 1 * N 1 0 := by
          refine mul_left_cancel₀ hb ?_
          linear_combination N 1 0 * b1 - N' 1 0 * a1
        refine ⟨t1, mul_left_cancel₀ hb ?_, mul_left_cancel₀ hb ?_⟩
        · linear_combination N' 0 1 * a3 - N 0 1 * b3 - (M 0 0 - M 1 1) * t1
        · linear_combination N 1 0 * b3 - N' 1 0 * a3
    · have t1 : N 0 1 * N' 1 0 = N' 0 1 * N 1 0 := by
        refine mul_left_cancel₀ ha ?_
        linear_combination N 0 1 * b1 - N' 0 1 * a1
      refine ⟨t1, mul_left_cancel₀ ha ?_, mul_left_cancel₀ ha ?_⟩
      · linear_combination N 0 1 * b2 - N' 0 1 * a2
      · linear_combination -(M 0 0 - M 1 1) * t1 - N 1 0 * b2 + N' 1 0 * a2
  obtain ⟨k1, k2, k3⟩ := key
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hN02, hN12, hN20, hN21, hN'02, hN'12, hN'20,
      hN'21] <;>
    first | ring1 | linear_combination k1 | linear_combination -k1 | linear_combination k2 |
      linear_combination -k2 | linear_combination k3

theorem le_center_of_normal_two [Finite K] (hK4 : 4 ≤ Nat.card K) (N : Subgroup SL(2, K))
    [hNn : N.Normal] (hN : ∀ a ∈ N, ∃ e : ℕ, a ^ 2 ^ e = 1) :
    N ≤ Subgroup.center SL(2, K) := by
  have h34 : 3 ≤ 2 ∨ ∃ s : Finset K, s.card = 4 :=
    Or.inr (CFSG.LinearGroups.exists_finset_card_eq_four hK4)
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2)
    le_rfl h34
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := K) (n := 2) le_rfl h34
  set Z := Subgroup.center SL(2, K)
  have hnorm : (N.map (QuotientGroup.mk' Z)).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective Z)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z)) with h | h
  · intro a ha
    have : QuotientGroup.mk' Z a = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.mem_map_of_mem _ ha
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
      intro x
      obtain ⟨a, ha, rfl⟩ : x ∈ N.map (QuotientGroup.mk' Z) := h ▸ Subgroup.mem_top x
      obtain ⟨e, he⟩ := hN a ha
      exact ⟨e, by rw [← map_pow, he, map_one]⟩
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent

theorem eq_top_of_three [Finite K] (hK4 : 4 ≤ Nat.card K) (N : Subgroup SL(2, K))
    (h3 : ∀ A : SL(2, K), A ^ 3 = 1 → A ∈ N) (hZ : Subgroup.center SL(2, K) ≤ N) :
    N = ⊤ := by
  have h34 : 3 ≤ 2 ∨ ∃ s : Finset K, s.card = 4 :=
    Or.inr (CFSG.LinearGroups.exists_finset_card_eq_four hK4)
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2)
    le_rfl h34
  set Z := Subgroup.center SL(2, K)
  set N₃ := Subgroup.normalClosure {A : SL(2, K) | A ^ 3 = 1} with hN₃
  have hN₃N : N₃ ≤ N := by
    rw [hN₃, Subgroup.normalClosure, Subgroup.closure_le]
    intro a ha
    obtain ⟨b, hb, hba⟩ := Group.mem_conjugatesOfSet_iff.mp ha
    obtain ⟨c, rfl⟩ := isConj_iff.mp hba
    apply h3
    rw [conj_pow, show b ^ 3 = 1 from hb, mul_one, mul_inv_cancel]
  have hnorm : (N₃.map (QuotientGroup.mk' Z)).Normal :=
    (Subgroup.normalClosure_normal).map _ (QuotientGroup.mk'_surjective Z)
  let a₀ : SL(2, K) := ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩
  have ha₀3 : a₀ ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    rw [pow_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a₀, Matrix.mul_apply, Fin.sum_univ_two]
  have ha₀Z : a₀ ∉ Z := by
    intro h
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have e2 := congrFun (congrFun hr 0) 1
    simp [a₀] at e2
  rcases hsimple.eq_bot_or_eq_top_of_normal (N₃.map (QuotientGroup.mk' Z)) with h | h
  · exfalso
    apply ha₀Z
    have : QuotientGroup.mk' Z a₀ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.mem_map_of_mem _ (Subgroup.subset_normalClosure ha₀3)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  · rw [eq_top_iff]
    intro A _
    obtain ⟨B, hB, hBA⟩ : QuotientGroup.mk' Z A ∈ N₃.map (QuotientGroup.mk' Z) :=
      h ▸ Subgroup.mem_top _
    have hz : B⁻¹ * A ∈ Z := QuotientGroup.eq.mp hBA
    have : A = B * (B⁻¹ * A) := by group
    rw [this]
    exact N.mul_mem (hN₃N hB) (hZ hz)

theorem blockEmb_neg_one : blockEmb (-1 : SL(2, K)) = sZero := by
  apply Subtype.ext
  rw [coe_blockEmb, coe_sZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, Matrix.SpecialLinearGroup.coe_neg]

theorem eq_one_or_eq_neg_one_of_mem_center {A : SL(2, K)} (hA : A ∈ Subgroup.center SL(2, K)) :
    A = 1 ∨ A = -1 := by
  obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr2
  have hrr : r * r = 1 := by rw [← sq]; exact hr2
  rcases mul_self_eq_one_iff.mp hrr with h | h
  · left
    apply Subtype.ext
    rw [← hr, h, Matrix.SpecialLinearGroup.coe_one, map_one]
  · right
    apply Subtype.ext
    rw [← hr, h, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, map_neg,
      map_one]

@[expose] def permZeroTwo : SL(3, K) :=
  ⟨!![0, 0, -1; 0, -1, 0; -1, 0, 0], by simp [Matrix.det_fin_three]⟩

@[expose] def permOneTwo : SL(3, K) :=
  ⟨!![-1, 0, 0; 0, 0, 1; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem exists_frame_sZero [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {x : SL(3, K)} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) : ∃ g : SL(3, K), g * x * g⁻¹ = sZero := by
  classical
  have hK2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  have hne1 : (-1 : K) ≠ 1 := fun h => hK2 (by linear_combination -h)
  set A := Subgroup.zpowers (proj 3 K x) with hA
  have hAe : IsElemAbelian 2 A := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨m, rfl⟩⟩ := a
      obtain ⟨_, ⟨n, rfl⟩⟩ := b
      simp only [Subgroup.coe_mul]
      rw [← zpow_add, ← zpow_add, add_comm]
    · rintro _ ⟨m, rfl⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow, hx2, map_one,
        one_zpow]
  have hxA : x ∈ CFSG.Quasithin.E22S.invLifts A hAe := ⟨Subgroup.mem_zpowers _, hx2⟩
  obtain ⟨g, hg⟩ := CFSG.Quasithin.E22S.exists_frame hp2 hAe
  have hd := CFSG.Quasithin.E22S.conj_eq_diagonal (hg x hxA)
  have hsq : ∀ i, CFSG.Quasithin.E22S.dg g x i * CFSG.Quasithin.E22S.dg g x i = 1 :=
    fun i => CFSG.Quasithin.E22S.dg_sq (hg x hxA) hx2 i
  have hprod := CFSG.Quasithin.E22S.dg_prod (hg x hxA)
  rw [Fin.prod_univ_three] at hprod
  set d := CFSG.Quasithin.E22S.dg g x with hd_def
  have hdiag : ∀ P : SL(3, K), P * P = 1 →
      ((P : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d * (P : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal ![-1, -1, 1]) → ∃ g : SL(3, K), g * x * g⁻¹ = sZero := by
    intro P hPP hPd
    refine ⟨P * g, ?_⟩
    have hPinv : P⁻¹ = P := (eq_inv_of_mul_eq_one_left hPP).symm
    apply Subtype.ext
    rw [coe_sZero, mul_inv_rev, hPinv, show P * g * x * (g⁻¹ * P) = P * (g * x * g⁻¹) * P by
      group, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hd]
    exact hPd
  rcases mul_self_eq_one_iff.mp (hsq 0) with h0 | h0 <;>
    rcases mul_self_eq_one_iff.mp (hsq 1) with h1 | h1 <;>
    rcases mul_self_eq_one_iff.mp (hsq 2) with h2 | h2 <;>
    rw [h0, h1, h2] at hprod
  · exfalso
    apply hx1
    have h1' : g * x * g⁻¹ = 1 := by
      apply Subtype.ext
      rw [hd, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h1']; group
  · exact absurd (by linear_combination hprod) hne1
  · exact absurd (by linear_combination hprod) hne1
  · refine hdiag permZeroTwo ?_ ?_
    · apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [permZeroTwo, Matrix.mul_apply, Fin.sum_univ_three]
    · ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      fin_cases i <;> fin_cases j <;>
        simp [permZeroTwo, h0, h1, h2]
  · exact absurd (by linear_combination hprod) hne1
  · refine hdiag permOneTwo ?_ ?_
    · apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [permOneTwo, Matrix.mul_apply, Fin.sum_univ_three]
    · ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      fin_cases i <;> fin_cases j <;>
        simp [permOneTwo, h0, h1, h2]
  · refine ⟨g, Subtype.ext ?_⟩
    rw [hd, coe_sZero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]
  · exact absurd (by linear_combination hprod) hne1

theorem isBlock_coe (hK2 : (2 : K) ≠ 0) {P : SL(3, K)} (hP : P * sZero = sZero * P) :
    IsBlock (P : Matrix (Fin 3) (Fin 3) K) :=
  isBlock_of_commute hK2 (by rw [← Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, hP])

theorem apply_two_two_mul (hK2 : (2 : K) ≠ 0) {P Q : SL(3, K)} (hP : P * sZero = sZero * P)
    (hQ : Q * sZero = sZero * Q) :
    ((P * Q : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 =
      (P : Matrix (Fin 3) (Fin 3) K) 2 2 * (Q : Matrix (Fin 3) (Fin 3) K) 2 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact mul_apply_two_two (isBlock_coe hK2 hP) (isBlock_coe hK2 hQ)

theorem apply_two_two_ne_zero (hK2 : (2 : K) ≠ 0) {P : SL(3, K)} (hP : P * sZero = sZero * P) :
    (P : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
  intro h
  have h1 := P.2
  rw [det_of_isBlock (isBlock_coe hK2 hP), h, mul_zero] at h1
  exact zero_ne_one h1

theorem blockEmb_commute_sZero (A : SL(2, K)) : blockEmb A * sZero = sZero * blockEmb A :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockEmb]
    exact commute_sZero_of_isBlock (isBlock_blockMat _))

theorem exists_blockEmb_eq {C : SL(3, K)} (hC : IsBlock (C : Matrix (Fin 3) (Fin 3) K))
    (h22 : (C : Matrix (Fin 3) (Fin 3) K) 2 2 = 1) : ∃ A : SL(2, K), blockEmb A = C := by
  set N : Matrix (Fin 3) (Fin 3) K := (C : Matrix (Fin 3) (Fin 3) K) with hN
  have hdet : N.det = 1 := C.2
  rw [det_of_isBlock hC, h22, mul_one] at hdet
  set B : Matrix (Fin 2) (Fin 2) K := !![N 0 0, N 0 1; N 1 0, N 1 1] with hB
  have hBdet : B.det = 1 := by rw [hB, Matrix.det_fin_two_of]; exact hdet
  refine ⟨⟨B, hBdet⟩, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
  obtain ⟨h02, h12, h20, h21⟩ := hC
  change blockMat B i j = N i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, hB, h02, h12, h20, h21, h22]

theorem commute_of_isBlockScalar {M N : Matrix (Fin 3) (Fin 3) K} (hM : IsBlockScalar M)
    (hN : IsBlockScalar N) : M * N = N * M := by
  obtain ⟨⟨a02, a12, a20, a21⟩, a01, a10, a00⟩ := hM
  obtain ⟨⟨b02, b12, b20, b21⟩, b01, b10, b00⟩ := hN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, a02, a12, a20, a21, a01, a10, b02, b12, b20, b21,
      b01, b10] <;> ring1

theorem four_le_card_of_charP [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p) :
    4 ≤ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  rw [Nat.card_eq_fintype_card, hn]
  calc 4 ≤ p := by omega
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ (n : ℕ) := Nat.pow_le_pow_right (by omega) n.2

theorem exists_central_involution {M : Type*} [Group M] {T : Subgroup M} [Finite T]
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ∃ t ∈ T, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ s ∈ T, s * t = t * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  have : Nontrivial (Subgroup.center T) := hT2.center_nontrivial
  have : Fintype (Subgroup.center T) := Fintype.ofFinite _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hT2.to_subgroup (Subgroup.center T))
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have := Finite.one_lt_card (α := Subgroup.center T)
    omega
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 2
    (show 2 ∣ Fintype.card (Subgroup.center T) by
      rw [← Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self 2 hn0)
  refine ⟨((z : T) : M), (z : T).2, ?_, ?_, ?_⟩
  · intro h
    have h1 : z = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hz
    omega
  · have h1 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have h2 := congrArg (fun w : Subgroup.center T => ((w : T) : M)) h1
    simpa using h2
  · intro s hs
    have h1 := Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩
    exact congrArg Subtype.val h1

theorem exists_smul_of_proj_commute {Z Y : SL(3, K)}
    (h : proj 3 K Z * proj 3 K Y = proj 3 K Y * proj 3 K Z) :
    ∃ c : K, c ^ 3 = 1 ∧ ((Z * Y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      c • ((Y * Z : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : proj 3 K (Y * Z) = proj 3 K (Z * Y) := by rw [map_mul, map_mul, h]
  exact Item211Lie2Proof.proj_eq_proj_iff.mp h1

theorem eq_bot_of_le_inn_projectiveSL [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p)
    {D T V W : Subgroup (MulAut (projectiveSL 3 K))}
    (hD9 : Nat.card D = 9) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTD : T ≤ Subgroup.centralizer (D : Set (MulAut (projectiveSL 3 K))))
    (hTi : T ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (hnab : ¬ ∀ a ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ⊓
        Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))),
      ∀ b ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ⊓
        Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))), a * b = b * a)
    (hVi : V ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (hV2 : IsPGroup 2 V) (hDV : D ≤ Subgroup.normalizer (V : Set (MulAut (projectiveSL 3 K))))
    (hVD : ⁅V, D⁆ = V) (hW2 : IsPGroup 2 W) (hVW : V ≤ W)
    (hWT : W ≤ Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))))
    (hτ : ∀ τ ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ⊓
        Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))),
      τ ^ 3 = 1 → τ ∈ Subgroup.normalizer (W : Set (MulAut (projectiveSL 3 K)))) : V = ⊥ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hK2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  have hK4 := four_le_card_of_charP (K := K) hp3
  have : Finite (MulAut (projectiveSL 3 K)) :=
    Finite.of_injective (fun σ : MulAut (projectiveSL 3 K) => (σ : projectiveSL 3 K → _))
      (fun a b h => MulEquiv.ext (congrFun h))
  have hZ := center_projectiveSL_three_eq_bot' (K := K)
  have hinj := conj_injective' hZ
  obtain ⟨t, htT, ht1, ht2, htc⟩ := exists_central_involution hT2 hT1
  obtain ⟨x, rfl⟩ := hTi htT
  have hx2 : x ^ 2 = 1 := hinj (by rw [map_pow, ht2, map_one])
  have hx1 : x ≠ 1 := fun h => ht1 (by rw [h, map_one])
  have hTx : ∀ y : projectiveSL 3 K, MulAut.conj y ∈ T → y * x = x * y := by
    intro y hy
    apply hinj
    rw [map_mul, map_mul]
    exact htc _ hy
  obtain ⟨X₀, hX₀2, hX₀⟩ : ∃ X₀ : SL(3, K), X₀ ^ 2 = 1 ∧ proj 3 K X₀ = x := by
    have hAe : IsElemAbelian 2 (Subgroup.zpowers x) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
      · obtain ⟨_, ⟨m, rfl⟩⟩ := a
        obtain ⟨_, ⟨n, rfl⟩⟩ := b
        simp only [Subgroup.coe_mul]
        rw [← zpow_add, ← zpow_add, add_comm]
      · rintro _ ⟨m, rfl⟩
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
    obtain ⟨X₀, hX₀, hX₀x⟩ := CFSG.Quasithin.E22S.exists_invLift hAe (Subgroup.mem_zpowers x)
    exact ⟨X₀, hX₀.2, hX₀x⟩
  have hX₀1 : X₀ ≠ 1 := fun h => hx1 (by rw [← hX₀, h, map_one])
  obtain ⟨g, hg⟩ := exists_frame_sZero hp2 hX₀2 hX₀1
  have hgX : g⁻¹ * sZero * g = X₀ := by rw [← hg]; group
  have hblock : ∀ Z : SL(3, K), proj 3 K Z * x = x * proj 3 K Z →
      g * Z * g⁻¹ * sZero = sZero * (g * Z * g⁻¹) := by
    intro Z hZx
    have hc : X₀ * Z = Z * X₀ := CFSG.Quasithin.E22S.commute_of_proj_commute_two hX₀2
      (by rw [hX₀]; exact hZx.symm)
    rw [← hg]
    calc g * Z * g⁻¹ * (g * X₀ * g⁻¹) = g * (Z * X₀) * g⁻¹ := by group
      _ = g * (X₀ * Z) * g⁻¹ := by rw [hc]
      _ = g * X₀ * g⁻¹ * (g * Z * g⁻¹) := by group
  have hTbs : ∀ y : projectiveSL 3 K, MulAut.conj y ∈ T → ∀ Y : SL(3, K), proj 3 K Y = y →
      IsBlockScalar ((g * Y * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
    intro y hy Y hY
    by_contra hns
    apply hnab
    have hMs := hblock Y (by rw [hY]; exact hTx y hy)
    have hMb := isBlock_coe hK2 hMs
    have hcomm : ∀ z : projectiveSL 3 K,
        MulAut.conj z ∈ Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))) →
        ∀ Z : SL(3, K), proj 3 K Z = z →
        IsBlock ((g * Z * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) ∧
        ((g * Y * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
            ((g * Z * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
          ((g * Z * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
            ((g * Y * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
      intro z hz Z hZ
      have hzs : ∀ s : projectiveSL 3 K, MulAut.conj s ∈ T → z * s = s * z := by
        intro s hs
        apply hinj
        rw [map_mul, map_mul]
        exact (Subgroup.mem_centralizer_iff.mp hz _ hs).symm
      have hNs := hblock Z (by rw [hZ]; exact hzs x htT)
      have hNb := isBlock_coe hK2 hNs
      refine ⟨hNb, ?_⟩
      obtain ⟨c, -, hc⟩ := exists_smul_of_proj_commute (Z := Z) (Y := Y)
        (by rw [hZ, hY]; exact hzs y hy)
      have e : ((g * Z * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
          ((g * Y * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
          c • (((g * Y * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
            ((g * Z * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) := by
        have h1 : ((g * Z * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
            ((g * Y * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
            (g : Matrix (Fin 3) (Fin 3) K) * ((Z * Y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
              ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
          rw [← Matrix.SpecialLinearGroup.coe_mul (g * Z * g⁻¹),
            show g * Z * g⁻¹ * (g * Y * g⁻¹) = g * (Z * Y) * g⁻¹ by group,
            Matrix.SpecialLinearGroup.coe_mul (g * (Z * Y)) g⁻¹,
            Matrix.SpecialLinearGroup.coe_mul g (Z * Y)]
        have h2 : ((g * Y * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
            ((g * Z * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
            (g : Matrix (Fin 3) (Fin 3) K) * ((Y * Z : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
              ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
          rw [← Matrix.SpecialLinearGroup.coe_mul (g * Y * g⁻¹),
            show g * Y * g⁻¹ * (g * Z * g⁻¹) = g * (Y * Z) * g⁻¹ by group,
            Matrix.SpecialLinearGroup.coe_mul (g * (Y * Z)) g⁻¹,
            Matrix.SpecialLinearGroup.coe_mul g (Y * Z)]
        rw [h1, h2, hc, Matrix.mul_smul, Matrix.smul_mul]
      have e22 := congrFun (congrFun e 2) 2
      rw [Matrix.smul_apply, mul_apply_two_two hNb hMb, mul_apply_two_two hMb hNb,
        smul_eq_mul] at e22
      have hc1 : c = 1 := by
        have h0 : (1 - c) * (((g * Z * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 *
            ((g * Y * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2) = 0 := by
          linear_combination e22
        rcases mul_eq_zero.mp h0 with h | h
        · linear_combination -h
        · exact absurd h (mul_ne_zero (apply_two_two_ne_zero hK2 hNs)
            (apply_two_two_ne_zero hK2 hMs))
      rw [hc1, one_smul] at e
      exact e.symm
    rintro a ⟨⟨z, rfl⟩, hzT⟩ b ⟨⟨z', rfl⟩, hz'T⟩
    obtain ⟨Z, rfl⟩ := proj_surjective 3 K z
    obtain ⟨Z', rfl⟩ := proj_surjective 3 K z'
    obtain ⟨hNb, hMN⟩ := hcomm _ hzT Z rfl
    obtain ⟨hN'b, hMN'⟩ := hcomm _ hz'T Z' rfl
    have hNN' := commute_of_commute_of_not_blockScalar hMb hNb hN'b hns hMN hMN'
    have hZZ' : Z * Z' = Z' * Z := by
      have h1 : g * Z * g⁻¹ * (g * Z' * g⁻¹) = g * Z' * g⁻¹ * (g * Z * g⁻¹) := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
        exact hNN'
      have h2 : g * (Z * Z') * g⁻¹ = g * (Z' * Z) * g⁻¹ := by
        calc g * (Z * Z') * g⁻¹ = g * Z * g⁻¹ * (g * Z' * g⁻¹) := by group
          _ = g * Z' * g⁻¹ * (g * Z * g⁻¹) := h1
          _ = g * (Z' * Z) * g⁻¹ := by group
      simpa using h2
    rw [← map_mul MulAut.conj, ← map_mul MulAut.conj, ← map_mul (proj 3 K),
      ← map_mul (proj 3 K), hZZ']
  let ι : SL(2, K) →* projectiveSL 3 K :=
    (proj 3 K).comp ((MulAut.conj g⁻¹).toMonoidHom.comp blockEmb)
  have hιapp : ∀ A : SL(2, K), ι A = proj 3 K (g⁻¹ * blockEmb A * g) := by
    intro A
    simp [ι]
  have hιT : ∀ A : SL(2, K),
      MulAut.conj (ι A) ∈ Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))) := by
    intro A
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨y, rfl⟩ := hTi hs
    obtain ⟨Y, rfl⟩ := proj_surjective 3 K y
    have hcm := commute_blockMat_of_isBlockScalar (hTbs _ hs Y rfl) A
    have h1 : g * Y * g⁻¹ * blockEmb A = blockEmb A * (g * Y * g⁻¹) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockEmb]
      exact hcm
    have h2 : Y * (g⁻¹ * blockEmb A * g) = (g⁻¹ * blockEmb A * g) * Y := by
      calc Y * (g⁻¹ * blockEmb A * g) = g⁻¹ * (g * Y * g⁻¹ * blockEmb A) * g := by group
        _ = g⁻¹ * (blockEmb A * (g * Y * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * blockEmb A * g) * Y := by group
    rw [hιapp, ← map_mul MulAut.conj, ← map_mul MulAut.conj, ← map_mul (proj 3 K),
      ← map_mul (proj 3 K), h2]
  have hιneg : ι (-1) = x := by
    rw [hιapp, blockEmb_neg_one, hgX, hX₀]
  have hWx : MulAut.conj x ∈ Subgroup.normalizer (W : Set (MulAut (projectiveSL 3 K))) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hWT hw) _ htT).symm)
  have hN : ∀ A : SL(2, K),
      MulAut.conj (ι A) ∈ Subgroup.normalizer (W : Set (MulAut (projectiveSL 3 K))) := by
    have htop := eq_top_of_three hK4
      ((Subgroup.normalizer (W : Set (MulAut (projectiveSL 3 K)))).comap
        ((MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).comp ι))
      (fun A hA => hτ _ (Subgroup.mem_inf.mpr ⟨⟨ι A, rfl⟩, hιT A⟩)
        (by rw [← map_pow, hA, map_one]))
      (fun z hz => by
        rcases eq_one_or_eq_neg_one_of_mem_center hz with rfl | rfl
        · exact Subgroup.one_mem _
        · rw [Subgroup.mem_comap, MonoidHom.comp_apply, hιneg]
          exact hWx)
    intro A
    have hA : A ∈ ((Subgroup.normalizer (W : Set (MulAut (projectiveSL 3 K)))).comap
        ((MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).comp ι)) := by
      rw [htop]
      exact Subgroup.mem_top A
    exact hA
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro A hA
    rw [hιapp, proj_eq_one_iff] at hA
    obtain ⟨c, -, hc⟩ := mem_scalars.mp hA
    have hE : ((blockEmb A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.scalar (Fin 3) (c : K) := by
      have e : blockEmb A = g * (g⁻¹ * blockEmb A * g) * g⁻¹ := by group
      rw [e, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hc,
        ← (Matrix.scalar_commute (c : K) (fun r' => Commute.all _ r') _).eq, Matrix.mul_assoc,
        ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.mul_one]
    have hc1 : (c : K) = 1 := by
      have h22 := congrFun (congrFun hE 2) 2
      simp [coe_blockEmb, blockMat] at h22
      exact h22.symm
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    have hij := congrFun (congrFun hE (Fin.castSucc i)) (Fin.castSucc j)
    fin_cases i <;> fin_cases j <;> simpa [coe_blockEmb, blockMat, hc1] using hij
  set 𝒲 := W.comap ((MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).comp ι)
    with h𝒲
  have h𝒲n : 𝒲.Normal := ⟨fun B hB A => by
    show MulAut.conj (ι (A * B * A⁻¹)) ∈ W
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hN A) _).mp hB⟩
  have h𝒲2 : ∀ a ∈ 𝒲, ∃ e : ℕ, a ^ 2 ^ e = 1 := by
    intro a ha
    obtain ⟨e, he⟩ := hW2 ⟨_, ha⟩
    refine ⟨e, hιinj (hinj ?_)⟩
    rw [map_pow, map_pow, map_one, map_one]
    simpa using congrArg Subtype.val he
  have h𝒲Z := le_center_of_normal_two hK4 𝒲 h𝒲2
  have hEs := blockEmb_commute_sZero (K := K)
  have hEinv : ∀ A : SL(2, K), (blockEmb A)⁻¹ * sZero = sZero * (blockEmb A)⁻¹ := by
    intro A
    rw [← map_inv]
    exact hEs A⁻¹
  have hWbs : ∀ w : projectiveSL 3 K, MulAut.conj w ∈ W → ∀ Wt : SL(3, K), proj 3 K Wt = w →
      IsBlockScalar ((g * Wt * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
    intro w hw Wt hWt
    have hwx : w * x = x * w := by
      apply hinj
      rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp (hWT hw) _ htT).symm
    have hMs : (g * Wt * g⁻¹) * sZero = sZero * (g * Wt * g⁻¹) :=
      hblock Wt (by rw [hWt]; exact hwx)
    have hMinv : (g * Wt * g⁻¹)⁻¹ * sZero = sZero * (g * Wt * g⁻¹)⁻¹ := by
      calc (g * Wt * g⁻¹)⁻¹ * sZero
          = (g * Wt * g⁻¹)⁻¹ * (sZero * (g * Wt * g⁻¹)) * (g * Wt * g⁻¹)⁻¹ := by group
        _ = (g * Wt * g⁻¹)⁻¹ * ((g * Wt * g⁻¹) * sZero) * (g * Wt * g⁻¹)⁻¹ := by rw [hMs]
        _ = sZero * (g * Wt * g⁻¹)⁻¹ := by group
    have hME : ∀ A : SL(2, K), (g * Wt * g⁻¹) * blockEmb A * sZero =
        sZero * ((g * Wt * g⁻¹) * blockEmb A) := by
      intro A
      rw [mul_assoc, hEs A, ← mul_assoc, hMs, mul_assoc]
    have hMEM : ∀ A : SL(2, K), (g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * sZero =
        sZero * ((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹) := by
      intro A
      rw [mul_assoc, hMinv, ← mul_assoc, hME A, mul_assoc]
    have hval : ∀ A : SL(2, K),
        (g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹ = 1 ∨
        (g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹ = sZero := by
      intro A
      have hCs : (g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹ * sZero =
          sZero * ((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹) := by
        rw [mul_assoc, hEinv A, ← mul_assoc, hMEM A, mul_assoc]
      have hC22 : (((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹ : SL(3, K)) :
          Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
        rw [apply_two_two_mul hK2 (hMEM A) (hEinv A), apply_two_two_mul hK2 (hME A) hMinv,
          apply_two_two_mul hK2 hMs (hEs A)]
        have h1 := apply_two_two_mul hK2 hMs hMinv
        have h2 := apply_two_two_mul hK2 (hEs A) (hEinv A)
        rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h1 h2
        linear_combination -(((blockEmb A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 *
          (((blockEmb A)⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2) * h1 - h2
      obtain ⟨A', hA'⟩ := exists_blockEmb_eq (isBlock_coe hK2 hCs) hC22
      have hA'W : A' ∈ 𝒲 := by
        show MulAut.conj (ι A') ∈ W
        have e : ι A' = w * ι A * w⁻¹ * (ι A)⁻¹ := by
          have e1 : g⁻¹ * ((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹) *
              g = Wt * (g⁻¹ * blockEmb A * g) * Wt⁻¹ * (g⁻¹ * blockEmb A * g)⁻¹ := by group
          rw [hιapp, hιapp, hA', e1, map_mul, map_mul, map_mul, map_inv, map_inv, hWt]
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
        have h1 : MulAut.conj (ι A) * (MulAut.conj w)⁻¹ * (MulAut.conj (ι A))⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hN A) _).mp (W.inv_mem hw)
        have h2 := W.mul_mem hw h1
        simpa only [mul_assoc] using h2
      rcases eq_one_or_eq_neg_one_of_mem_center (h𝒲Z hA'W) with h | h
      · left
        rw [← hA', h, map_one]
      · right
        rw [← hA', h, blockEmb_neg_one]
    have hcomm_val : ∀ A B : SL(2, K),
        ((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹) *
          ((g * Wt * g⁻¹) * blockEmb B * (g * Wt * g⁻¹)⁻¹ * (blockEmb B)⁻¹) =
        ((g * Wt * g⁻¹) * blockEmb B * (g * Wt * g⁻¹)⁻¹ * (blockEmb B)⁻¹) *
          ((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹) := by
      intro A B
      rcases hval A with h | h <;> rcases hval B with h' | h' <;> rw [h, h'] <;> simp
    have hcent_val : ∀ A B : SL(2, K),
        ((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹) *
          ((g * Wt * g⁻¹) * blockEmb B * (g * Wt * g⁻¹)⁻¹ * (blockEmb B)⁻¹) =
        ((g * Wt * g⁻¹) * blockEmb B * (g * Wt * g⁻¹)⁻¹ * (blockEmb B)⁻¹) *
          ((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹) := by
      intro A B
      rcases hval B with h | h <;> rw [h]
      · simp
      · exact hMEM A
    let φ : SL(2, K) →* SL(3, K) :=
      { toFun := fun A => (g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹
        map_one' := by simp
        map_mul' := fun A B => by
          calc (g * Wt * g⁻¹) * blockEmb (A * B) * (g * Wt * g⁻¹)⁻¹ * (blockEmb (A * B))⁻¹
              = ((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹) *
                  ((g * Wt * g⁻¹) * blockEmb B * (g * Wt * g⁻¹)⁻¹ * (blockEmb B)⁻¹) *
                  (blockEmb A)⁻¹ := by rw [map_mul]; group
            _ = ((g * Wt * g⁻¹) * blockEmb B * (g * Wt * g⁻¹)⁻¹ * (blockEmb B)⁻¹) *
                  ((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹) * (blockEmb A)⁻¹ := by
                rw [hcent_val A B]
            _ = ((g * Wt * g⁻¹) * blockEmb B * (g * Wt * g⁻¹)⁻¹ * (blockEmb B)⁻¹) *
                  ((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹) := by
                group
            _ = _ := hcomm_val B A }
    have hφ1 : ∀ A : SL(2, K), φ A = 1 := by
      have : Group.IsPerfect SL(2, K) :=
        CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K)
          (CFSG.LinearGroups.exists_finset_card_eq_four hK4)
      have hle : commutator SL(2, K) ≤ φ.ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm_val a b
      intro A
      exact hle (by rw [Group.IsPerfect.commutator_eq_top]; exact Subgroup.mem_top A)
    have hMcomm : ∀ A : SL(2, K), ((g * Wt * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
        blockMat A = blockMat A * ((g * Wt * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
      intro A
      have h1 : (g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹ = 1 := hφ1 A
      have h2 : (g * Wt * g⁻¹) * blockEmb A = blockEmb A * (g * Wt * g⁻¹) := by
        calc (g * Wt * g⁻¹) * blockEmb A
            = ((g * Wt * g⁻¹) * blockEmb A * (g * Wt * g⁻¹)⁻¹ * (blockEmb A)⁻¹) *
              (blockEmb A * (g * Wt * g⁻¹)) := by group
          _ = blockEmb A * (g * Wt * g⁻¹) := by rw [h1, one_mul]
      have h3 := congrArg (fun P : SL(3, K) => (P : Matrix (Fin 3) (Fin 3) K)) h2
      simpa only [Matrix.SpecialLinearGroup.coe_mul, coe_blockEmb] using h3
    let u : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    let l : SL(2, K) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    exact isBlockScalar_of_commute_transvections (isBlock_coe hK2 hMs) (hMcomm u) (hMcomm l)
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    obtain ⟨v, rfl⟩ := hVi ha
    obtain ⟨v', rfl⟩ := hVi hb
    obtain ⟨Vt, rfl⟩ := proj_surjective 3 K v
    obtain ⟨Vt', rfl⟩ := proj_surjective 3 K v'
    have h1 : g * Vt * g⁻¹ * (g * Vt' * g⁻¹) = g * Vt' * g⁻¹ * (g * Vt * g⁻¹) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact commute_of_isBlockScalar (hWbs _ (hVW ha) Vt rfl) (hWbs _ (hVW hb) Vt' rfl)
    have h2 : Vt * Vt' = Vt' * Vt := by
      have h3 : g * (Vt * Vt') * g⁻¹ = g * (Vt' * Vt) * g⁻¹ := by
        calc g * (Vt * Vt') * g⁻¹ = g * Vt * g⁻¹ * (g * Vt' * g⁻¹) := by group
          _ = g * Vt' * g⁻¹ * (g * Vt * g⁻¹) := h1
          _ = g * (Vt' * Vt) * g⁻¹ := by group
      simpa using h3
    rw [← map_mul MulAut.conj, ← map_mul MulAut.conj, ← map_mul (proj 3 K),
      ← map_mul (proj 3 K), h2]
  have hVfix : ∀ a ∈ V, a ^ 2 = 1 → a = 1 ∨ a = MulAut.conj x := by
    intro a ha ha2
    obtain ⟨v, rfl⟩ := hVi ha
    obtain ⟨Vt, rfl⟩ := proj_surjective 3 K v
    have hv2 : proj 3 K (Vt ^ 2) = 1 := by
      rw [map_pow]
      exact hinj (by rw [map_pow, ha2, map_one])
    obtain ⟨⟨h02, h12, h20, h21⟩, h01, h10, h00⟩ := hWbs _ (hVW ha) Vt rfl
    have hVt2 := proj_eq_one_iff.mp hv2
    have hN2 : (g * Vt * g⁻¹) ^ 2 = Vt ^ 2 := by
      rw [conj_pow]
      have hc := Subgroup.mem_center_iff.mp ((scalars_le_center 3 K) hVt2) g
      rw [hc, mul_inv_cancel_right]
    obtain ⟨ζ, -, hζ⟩ := mem_scalars.mp hVt2
    have hNN : ((g * Vt * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
        ((g * Vt * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (ζ : K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← pow_two, hN2, hζ]
    have e00 := congrFun (congrFun hNN 0) 0
    have e22 := congrFun (congrFun hNN 2) 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h20, h21, h12, mul_zero,
      add_zero, zero_add, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at e00 e22
    have hdet := (g * Vt * g⁻¹).2
    rw [det_of_isBlock ⟨h02, h12, h20, h21⟩, h01, h10, ← h00] at hdet
    set m := ((g * Vt * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 with hm
    set β := ((g * Vt * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 with hβ
    have hm3 : m ^ 3 = 1 := by
      have : (β - m) * (β + m) = 0 := by linear_combination e00 - e22
      rcases mul_eq_zero.mp this with h | h
      · have hb : β = m := sub_eq_zero.mp h
        rw [hb] at hdet
        linear_combination hdet
      · have hb : β = -m := by linear_combination h
        rw [hb] at hdet
        linear_combination hdet
    have hconj : ∀ S : SL(3, K), ((g * Vt * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
        m • (S : Matrix (Fin 3) (Fin 3) K) →
        (Vt : Matrix (Fin 3) (Fin 3) K) =
          m • ((g⁻¹ * S * g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
      intro S hS
      have e1 : Vt = g⁻¹ * (g * Vt * g⁻¹) * g := by group
      rw [e1, Matrix.SpecialLinearGroup.coe_mul (g⁻¹ * (g * Vt * g⁻¹)) g,
        Matrix.SpecialLinearGroup.coe_mul g⁻¹ (g * Vt * g⁻¹), hS,
        Matrix.SpecialLinearGroup.coe_mul (g⁻¹ * S) g, Matrix.SpecialLinearGroup.coe_mul g⁻¹ S,
        Matrix.mul_smul, Matrix.smul_mul]
    have : (β - m) * (β + m) = 0 := by linear_combination e00 - e22
    rcases mul_eq_zero.mp this with h | h
    · left
      have hb : β = m := sub_eq_zero.mp h
      have hS : ((g * Vt * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
          m • ((1 : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h20, h21, h12, ← h00, hb, ← hm, ← hβ]
      have h1 := hconj 1 hS
      rw [show g⁻¹ * 1 * g = 1 by group] at h1
      have h2 : proj 3 K 1 = proj 3 K Vt := Item211Lie2Proof.proj_eq_proj_iff.mpr ⟨m, hm3, h1⟩
      rw [← h2, map_one, map_one]
    · right
      have hb : β = -m := by linear_combination h
      have hS : ((g * Vt * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
          m • ((sZero : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
        rw [coe_sZero]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h20, h21, h12, ← h00, hb, ← hm, ← hβ]
      have h1 := hconj sZero hS
      rw [hgX] at h1
      have h2 : proj 3 K X₀ = proj 3 K Vt := Item211Lie2Proof.proj_eq_proj_iff.mpr ⟨m, hm3, h1⟩
      rw [← h2, hX₀]
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD9]; norm_num)
  refine eq_bot_of_comm_of_fixed hVc (by rw [hD9]; decide) hV2 hDV hVD fun v hv hv2 d hd => ?_
  rcases hVfix v hv hv2 with rfl | rfl
  · rw [one_mul, mul_one]
  · exact Subgroup.mem_centralizer_iff.mp (hTD htT) d hd

@[expose] def L3PlusOuterFor (Y : Type*) [Group Y] : Prop :=
  ∀ D T V W : Subgroup (MulAut Y), IsElemAbelian 3 D → Nat.card D = 9 → IsPGroup 2 T →
    T ≠ ⊥ → T ≤ Subgroup.centralizer (D : Set (MulAut Y)) →
    ¬ (∀ a ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer
        ((T ⊓ (MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)),
      ∀ b ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer
        ((T ⊓ (MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)),
      a * b = b * a) →
    ¬ T ≤ (MulAut.conj : Y →* MulAut Y).range →
    V ≤ (MulAut.conj : Y →* MulAut Y).range → IsPGroup 2 V →
    D ≤ Subgroup.normalizer (V : Set (MulAut Y)) → ⁅V, D⁆ = V →
    V ≤ Subgroup.centralizer (T : Set (MulAut Y)) → IsPGroup 2 W → V ≤ W →
    W ≤ Subgroup.centralizer (T : Set (MulAut Y)) →
    (∀ τ ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer (T : Set (MulAut Y)),
      τ ^ 3 = 1 → τ ∈ Subgroup.normalizer (W : Set (MulAut Y))) →
    V = ⊥

theorem l3PlusCoreFor_projectiveSL_of_outer [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp3 : 3 < p) (h : L3PlusOuterFor (projectiveSL 3 K)) : L3PlusCoreFor (projectiveSL 3 K) := by
  intro D T V W hDe hD9 hT2 hT1 hTD hnab hVi hV2 hDV hVD hVT hW2 hVW hWT hτ
  by_cases hTi : T ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range
  · have hTT : T ⊓ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range = T :=
      inf_eq_left.mpr hTi
    rw [hTT] at hnab
    exact eq_bot_of_le_inn_projectiveSL hp3 hD9 hT2 hT1 hTD hTi hnab hVi hV2 hDV hVD hW2 hVW
      hWT hτ
  · exact h D T V W hDe hD9 hT2 hT1 hTD hnab hTi hVi hV2 hDV hVD hVT hW2 hVW hWT hτ

end Linear

end Item211Lie2Proof

open Item211Lie2Proof
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

@[expose] def KS211L3PlusLinearOuter : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p], 3 < p →
    Nat.card K % 3 = 1 → L3PlusOuterFor (projectiveSL 3 K)

theorem ks211L3PlusLinearCore_of_outer (h : KS211L3PlusLinearOuter) : KS211L3PlusLinearCore :=
  fun K _ _ p _ _ hp3 hK => l3PlusCoreFor_projectiveSL_of_outer hp3 (h K p hp3 hK)

end CFSG.RankThree.PartTwo.Sec21
