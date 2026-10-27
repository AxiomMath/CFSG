module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

section Orbit

variable {G : Type} [Group G]

theorem exists_zpow_mul_of_mem_sup {a b x : G} (hab : a * b = b * a)
    (hx : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) : ∃ i j : ℤ, x = a ^ i * b ^ j := by
  have hc : ∀ i j : ℤ, b ^ j * a ^ i = a ^ i * b ^ j := fun i j =>
    (Commute.zpow_zpow hab i j).eq.symm
  let P : Subgroup G :=
    { carrier := {g | ∃ i j : ℤ, g = a ^ i * b ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        refine ⟨i + k, j + l, ?_⟩
        rw [_root_.zpow_add, _root_.zpow_add]
        calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by group
          _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [hc]
          _ = a ^ i * a ^ k * (b ^ j * b ^ l) := by group
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨-i, -j, ?_⟩
        rw [_root_.mul_inv_rev, ← _root_.zpow_neg, ← _root_.zpow_neg, hc] }
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ P := sup_le
    (Subgroup.zpowers_le.mpr ⟨1, 0, by simp⟩) (Subgroup.zpowers_le.mpr ⟨0, 1, by simp⟩)
  exact hle hx

theorem zpow_emod_three {a : G} (h : a ^ 3 = 1) (i : ℤ) : a ^ i = a ^ (i % 3) := by
  have h3 : a ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, h]
  conv_lhs => rw [← Int.mul_ediv_add_emod i 3]
  rw [_root_.zpow_add, _root_.zpow_mul, h3, _root_.one_zpow, one_mul]

theorem exists_conj_eq_of_q8 {x₁ x₂ n₁ n₂ : G} (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1)
    (h2 : x₂ ^ 3 = 1) (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹) (hF2 : n₁ * x₂ * n₁⁻¹ = x₁)
    (hN1 : n₂ * x₁ * n₂⁻¹ = x₂⁻¹ * x₁⁻¹) {x : G}
    (hx : x ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) (hx1 : x ≠ 1) :
    ∃ n ∈ Subgroup.closure {n₁, n₂}, n * x₁ * n⁻¹ = x := by
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup h12 hx
  rw [zpow_emod_three h1 i, zpow_emod_three h2 j] at hx1 ⊢
  have hF1' : n₁ * x₁⁻¹ * n₁⁻¹ = x₂ := by
    rw [show n₁ * x₁⁻¹ * n₁⁻¹ = (n₁ * x₁ * n₁⁻¹)⁻¹ by group, hF1, inv_inv]
  have hF2' : n₁ * x₂⁻¹ * n₁⁻¹ = x₁⁻¹ := by
    rw [show n₁ * x₂⁻¹ * n₁⁻¹ = (n₁ * x₂ * n₁⁻¹)⁻¹ by group, hF2]
  have hN1' : n₂ * x₁⁻¹ * n₂⁻¹ = x₁ * x₂ := by
    rw [show n₂ * x₁⁻¹ * n₂⁻¹ = (n₂ * x₁ * n₂⁻¹)⁻¹ by group, hN1, _root_.mul_inv_rev, inv_inv,
      inv_inv]
  have hsq1 : x₁ ^ (2 : ℤ) = x₁⁻¹ := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h1])
  have hsq2 : x₂ ^ (2 : ℤ) = x₂⁻¹ := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h2])
  have hc' : x₂⁻¹ * x₁ = x₁ * x₂⁻¹ := by
    calc x₂⁻¹ * x₁ = x₂⁻¹ * (x₁ * x₂) * x₂⁻¹ := by group
      _ = x₂⁻¹ * (x₂ * x₁) * x₂⁻¹ := by rw [h12]
      _ = x₁ * x₂⁻¹ := by group
  have hc'' : x₂⁻¹ * x₁⁻¹ = x₁⁻¹ * x₂⁻¹ := by
    rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, h12]
  have hn1 : n₁ ∈ Subgroup.closure {n₁, n₂} := Subgroup.subset_closure (by simp)
  have hn2 : n₂ ∈ Subgroup.closure {n₁, n₂} := Subgroup.subset_closure (by simp)
  have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;> rw [hi, hj] at hx1 ⊢ <;>
    simp only [zpow_zero, zpow_one, one_mul, mul_one, hsq1, hsq2] at hx1 ⊢
  · exact absurd rfl hx1
  ·
    refine ⟨n₁ * n₁ * n₁, mul_mem (mul_mem hn1 hn1) hn1, ?_⟩
    calc n₁ * n₁ * n₁ * x₁ * (n₁ * n₁ * n₁)⁻¹ =
        n₁ * (n₁ * (n₁ * x₁ * n₁⁻¹) * n₁⁻¹) * n₁⁻¹ := by group
      _ = x₂ := by rw [hF1, hF2', hF1']
  · exact ⟨n₁, hn1, hF1⟩
  · exact ⟨1, one_mem _, by group⟩
  ·
    refine ⟨n₂ * (n₁ * n₁), mul_mem hn2 (mul_mem hn1 hn1), ?_⟩
    calc n₂ * (n₁ * n₁) * x₁ * (n₂ * (n₁ * n₁))⁻¹ =
        n₂ * (n₁ * (n₁ * x₁ * n₁⁻¹) * n₁⁻¹) * n₂⁻¹ := by group
      _ = x₁ * x₂ := by rw [hF1, hF2', hN1']
  ·
    refine ⟨n₁ * n₂ * (n₁ * n₁), mul_mem (mul_mem hn1 hn2) (mul_mem hn1 hn1), ?_⟩
    calc n₁ * n₂ * (n₁ * n₁) * x₁ * (n₁ * n₂ * (n₁ * n₁))⁻¹ =
        n₁ * (n₂ * (n₁ * (n₁ * x₁ * n₁⁻¹) * n₁⁻¹) * n₂⁻¹) * n₁⁻¹ := by group
      _ = n₁ * (x₁ * x₂) * n₁⁻¹ := by rw [hF1, hF2', hN1']
      _ = n₁ * x₁ * n₁⁻¹ * (n₁ * x₂ * n₁⁻¹) := by group
      _ = x₁ * x₂⁻¹ := by rw [hF1, hF2, hc']
  · refine ⟨n₁ * n₁, mul_mem hn1 hn1, ?_⟩
    calc n₁ * n₁ * x₁ * (n₁ * n₁)⁻¹ = n₁ * (n₁ * x₁ * n₁⁻¹) * n₁⁻¹ := by group
      _ = x₁⁻¹ := by rw [hF1, hF2']
  ·
    refine ⟨n₁ * n₂, mul_mem hn1 hn2, ?_⟩
    calc n₁ * n₂ * x₁ * (n₁ * n₂)⁻¹ = n₁ * (n₂ * x₁ * n₂⁻¹) * n₁⁻¹ := by group
      _ = n₁ * x₂⁻¹ * n₁⁻¹ * (n₁ * x₁⁻¹ * n₁⁻¹) := by rw [hN1]; group
      _ = x₁⁻¹ * x₂ := by rw [hF2', hF1']
  · refine ⟨n₂, hn2, ?_⟩
    rw [hN1, hc'']

variable [Finite G]

theorem transitive_of_q8 {M : Subgroup G} {x₁ x₂ n₁ n₂ : G} (h12 : x₁ * x₂ = x₂ * x₁)
    (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹)
    (hF2 : n₁ * x₂ * n₁⁻¹ = x₁) (hN1 : n₂ * x₁ * n₂⁻¹ = x₂⁻¹ * x₁⁻¹)
    (hN2 : n₂ * x₂ * n₂⁻¹ = x₁ * x₂ * x₁) (hn₁ : n₁ ∈ M) (hn₂ : n₂ ∈ M) :
    ∀ x ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, x ≠ 1 →
      ∀ y ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, y ≠ 1 →
        ∃ n ∈ M ⊓ Subgroup.normalizer
          ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G), n * x * n⁻¹ = y := by
  set E := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ with hE
  have hconj : ∀ n : G, n * x₁ * n⁻¹ ∈ E → n * x₂ * n⁻¹ ∈ E →
      n ∈ Subgroup.normalizer (E : Set G) := by
    intro n hn1 hn2
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup h12 hx
    have e1 : n * (x₁ ^ i * x₂ ^ j) * n⁻¹ = (n * x₁ * n⁻¹) ^ i * (n * x₂ * n⁻¹) ^ j := by
      rw [conj_zpow, conj_zpow]
      group
    rw [e1]
    exact mul_mem (zpow_mem hn1 i) (zpow_mem hn2 j)
  have hx₁E : x₁ ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hx₂E : x₂ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
  have hN₁ : n₁ ∈ Subgroup.normalizer (E : Set G) := hconj n₁
    (by rw [hF1]; exact inv_mem hx₂E) (by rw [hF2]; exact hx₁E)
  have hN₂ : n₂ ∈ Subgroup.normalizer (E : Set G) := hconj n₂
    (by rw [hN1]; exact mul_mem (inv_mem hx₂E) (inv_mem hx₁E))
    (by rw [hN2]; exact mul_mem (mul_mem hx₁E hx₂E) hx₁E)
  have hle : Subgroup.closure {n₁, n₂} ≤ M ⊓ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.closure_le]
    intro n hn
    rcases hn with rfl | hn
    · exact ⟨hn₁, hN₁⟩
    · rw [Set.mem_singleton_iff] at hn
      subst hn
      exact ⟨hn₂, hN₂⟩
  intro x hx hx1 y hy hy1
  obtain ⟨n, hn, hnx⟩ := exists_conj_eq_of_q8 h12 h1 h2 hF1 hF2 hN1 hx hx1
  obtain ⟨m, hm, hmy⟩ := exists_conj_eq_of_q8 h12 h1 h2 hF1 hF2 hN1 hy hy1
  refine ⟨m * n⁻¹, hle (mul_mem hm (inv_mem hn)), ?_⟩
  rw [← hnx, ← hmy]
  group

end Orbit

section Fourier

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] def fourierMat (τ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 1, 1; 1, τ, τ ^ 2; 1, τ ^ 2, τ]

@[expose] def fourierBar (τ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 1, 1; 1, τ ^ 2, τ; 1, τ, τ ^ 2]

theorem fourierMat_mul_fourierBar {τ : K} (hs : 1 + τ + τ ^ 2 = 0) :
    fourierMat τ * fourierBar τ = (3 : K) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fourierMat, fourierBar, mul_apply, Fin.sum_univ_three] <;>
    grind

theorem fourierBar_mul_fourierMat {τ : K} (hs : 1 + τ + τ ^ 2 = 0) :
    fourierBar τ * fourierMat τ = (3 : K) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fourierMat, fourierBar, mul_apply, Fin.sum_univ_three] <;>
    grind

theorem one_sub_ne_zero_of_sum {τ : K} (h3 : (3 : K) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0) :
    1 - τ ≠ 0 := by
  intro h
  apply h3
  have : τ = 1 := by linear_combination -h
  rw [this] at hs
  linear_combination hs

@[expose] noncomputable def fourierGL {τ : K} (h3 : (3 : K) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0) :
    GL (Fin 3) K :=
  ⟨(1 - τ)⁻¹ • fourierMat τ, ((1 - τ) / 3) • fourierBar τ,
    by
      rw [Matrix.smul_mul, Matrix.mul_smul, fourierMat_mul_fourierBar hs, smul_smul, smul_smul]
      rw [show (1 - τ)⁻¹ * ((1 - τ) / 3) * 3 = 1 by
        field_simp [one_sub_ne_zero_of_sum h3 hs]]
      exact one_smul _ _,
    by
      rw [Matrix.smul_mul, Matrix.mul_smul, fourierBar_mul_fourierMat hs, smul_smul, smul_smul]
      rw [show (1 - τ) / 3 * (1 - τ)⁻¹ * 3 = 1 by
        field_simp [one_sub_ne_zero_of_sum h3 hs]]
      exact one_smul _ _⟩

theorem coe_fourierGL {τ : K} (h3 : (3 : K) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0) :
    ((fourierGL h3 hs : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (1 - τ)⁻¹ • fourierMat τ :=
  rfl

theorem det_fourierGL {τ : K} (h3 : (3 : K) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0) :
    ((fourierGL h3 hs : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h1 := one_sub_ne_zero_of_sum h3 hs
  rw [coe_fourierGL, Matrix.det_smul, Fintype.card_fin, fourierMat, det_fin_three]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
    cons_val_fin_one, head_cons, tail_cons, head_fin_const]
  field_simp
  grind

theorem fourierGL_mem_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (h3 : (3 : K) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0) :
    fourierGL h3 hs ∈ slPi π 3 (p ^ f) K := by
  cases π
  · have h := hK.unitary
    rw [mem_slPi_false h]
    refine ⟨det_fourierGL h3 hs, ?_⟩
    have hbτ : h.bar τ = τ ^ 2 := by
      have hn := pow_succ_eq_one_of_modThree hq hτ
      rw [h.bar_apply]
      calc τ ^ p ^ f = τ ^ p ^ f * (τ * τ ^ 2) := by
            rw [← pow_succ', hτ, mul_one]
        _ = τ ^ (p ^ f + 1) * τ ^ 2 := by ring
        _ = τ ^ 2 := by rw [hn, one_mul]
    have h1 := one_sub_ne_zero_of_sum h3 hs
    have h2 : 1 - τ ^ 2 ≠ 0 := by
      intro h0
      apply h3
      have : (1 - τ) * (1 - τ ^ 2) = 3 := by linear_combination hτ - hs
      rw [← this, h0, mul_zero]
    rw [coe_fourierGL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fourierMat, mul_apply, Fin.sum_univ_three, map_inv₀, hbτ] <;>
      field_simp <;> grind
  · rw [mem_slPi_true]
    exact det_fourierGL h3 hs

end Fourier

section Relations

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] noncomputable def phaseGL {τ : K} (hτ : τ ^ 3 = 1) : GL (Fin 3) K :=
  diagUnits 1 1 (Units.mk0 τ (fun h => by simp [h] at hτ))

theorem coe_phaseGL {τ : K} (hτ : τ ^ 3 = 1) :
    ((phaseGL hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, 0; 0, 0, τ] := by
  rw [phaseGL, coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem phaseGL_mem_glPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) : phaseGL hτ ∈ glPi π 3 (p ^ f) K := by
  refine diagUnits_mem_glPi hK (one_mem _) (one_mem _) (cube_root_mem_qSubPi hq ?_)
  rw [mem_rootsOfUnity]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ, Units.val_one])

theorem cycThree_pow_three : (cycThree : GL (Fin 3) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_cycThree, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, mul_apply, Fin.sum_univ_three]

theorem mk_eq_of_coe_eq_smul {M N : GL (Fin 3) K} {a : K}
    (h : (M : Matrix (Fin 3) (Fin 3) K) = a • (N : Matrix (Fin 3) (Fin 3) K)) :
    ProjGenLinGroup.mk M = ProjGenLinGroup.mk N := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    have hM := M.isUnit
    rw [h] at hM
    exact not_isUnit_zero hM
  have hM : M = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 a ha) * N := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, h, Units.val_mk0, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  rw [hM, map_mul, mk_eq_one_iff_mem_statedScalars.mpr ⟨_, rfl⟩, one_mul]

theorem coe_cycThree_inv : ((cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![0, 1, 0; 0, 0, 1; 1, 0, 0] :=
  rfl

variable {τ : K} (hτ : τ ^ 3 = 1) (h3 : (3 : K) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0)

include hs in
theorem mk_fourier_diagTau :
    ProjGenLinGroup.mk (fourierGL h3 hs) * ProjGenLinGroup.mk (diagTau hτ) *
      (ProjGenLinGroup.mk (fourierGL h3 hs))⁻¹ = (ProjGenLinGroup.mk cycThree)⁻¹ := by
  have h : ProjGenLinGroup.mk (fourierGL h3 hs * diagTau hτ) =
      ProjGenLinGroup.mk (cycThree⁻¹ * fourierGL h3 hs) := by
    refine mk_eq_of_coe_eq_smul (a := τ) ?_
    rw [Units.val_mul, Units.val_mul, coe_fourierGL, coe_diagTau, coe_cycThree_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fourierMat, mul_apply, Fin.sum_univ_three] <;> grind
  rw [map_mul, map_mul, map_inv] at h
  rw [h]
  group

include hs in
theorem mk_fourier_cycThree :
    ProjGenLinGroup.mk (fourierGL h3 hs) * ProjGenLinGroup.mk cycThree *
      (ProjGenLinGroup.mk (fourierGL h3 hs))⁻¹ = ProjGenLinGroup.mk (diagTau hτ) := by
  have h : ProjGenLinGroup.mk (fourierGL h3 hs * cycThree) =
      ProjGenLinGroup.mk (diagTau hτ * fourierGL h3 hs) := by
    refine mk_eq_of_coe_eq_smul (a := τ ^ 2) ?_
    rw [Units.val_mul, Units.val_mul, coe_fourierGL, coe_diagTau, coe_cycThree]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fourierMat, mul_apply, Fin.sum_univ_three] <;> grind
  rw [map_mul, map_mul] at h
  rw [h]
  group

theorem mk_phase_diagTau :
    ProjGenLinGroup.mk (phaseGL hτ) * ProjGenLinGroup.mk (diagTau hτ) *
      (ProjGenLinGroup.mk (phaseGL hτ))⁻¹ = ProjGenLinGroup.mk (diagTau hτ) := by
  have h : phaseGL hτ * diagTau hτ = diagTau hτ * phaseGL hτ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_phaseGL, coe_diagTau]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]
  rw [← map_mul, h, map_mul]
  group

theorem mk_phase_cycThree :
    ProjGenLinGroup.mk (phaseGL hτ) * ProjGenLinGroup.mk cycThree *
      (ProjGenLinGroup.mk (phaseGL hτ))⁻¹ =
        ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk cycThree := by
  have h : ProjGenLinGroup.mk (phaseGL hτ * cycThree) =
      ProjGenLinGroup.mk (diagTau hτ * cycThree * phaseGL hτ) := by
    refine mk_eq_of_coe_eq_smul (a := τ) ?_
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_phaseGL, coe_diagTau, coe_cycThree]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> grind
  rw [map_mul, map_mul, map_mul] at h
  rw [h]
  group

theorem mk_diagTau_cycThree :
    ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk cycThree =
      ProjGenLinGroup.mk cycThree * ProjGenLinGroup.mk (diagTau hτ) := by
  have h : ProjGenLinGroup.mk (cycThree * diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ * cycThree) := by
    refine mk_eq_of_coe_eq_smul (a := τ ^ 2) ?_
    rw [Units.val_mul, Units.val_mul, coe_diagTau, coe_cycThree]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> grind
  rw [map_mul, map_mul] at h
  exact h.symm

include hs in
theorem mk_conjFourier_diagTau :
    ProjGenLinGroup.mk (phaseGL hτ * fourierGL h3 hs * (phaseGL hτ)⁻¹) *
      ProjGenLinGroup.mk (diagTau hτ) *
        (ProjGenLinGroup.mk (phaseGL hτ * fourierGL h3 hs * (phaseGL hτ)⁻¹))⁻¹ =
      (ProjGenLinGroup.mk cycThree)⁻¹ * (ProjGenLinGroup.mk (diagTau hτ))⁻¹ := by
  set T := ProjGenLinGroup.mk (phaseGL hτ)
  set F := ProjGenLinGroup.mk (fourierGL h3 hs)
  set d := ProjGenLinGroup.mk (diagTau hτ)
  set c := ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)
  have R1 : F * d * F⁻¹ = c⁻¹ := mk_fourier_diagTau hτ h3 hs
  have R3 : T * d * T⁻¹ = d := mk_phase_diagTau hτ
  have R4 : T * c * T⁻¹ = d * c := mk_phase_cycThree hτ
  have R3' : T⁻¹ * d * T = d := by
    calc T⁻¹ * d * T = T⁻¹ * (T * d * T⁻¹) * T := by rw [R3]
      _ = d := by group
  rw [map_mul, map_mul, map_inv]
  calc T * F * T⁻¹ * d * (T * F * T⁻¹)⁻¹ = T * (F * (T⁻¹ * d * T) * F⁻¹) * T⁻¹ := by group
    _ = T * (F * d * F⁻¹) * T⁻¹ := by rw [R3']
    _ = (T * c * T⁻¹)⁻¹ := by rw [R1]; group
    _ = c⁻¹ * d⁻¹ := by rw [R4]; group

include hs in
theorem mk_conjFourier_cycThree :
    ProjGenLinGroup.mk (phaseGL hτ * fourierGL h3 hs * (phaseGL hτ)⁻¹) *
      ProjGenLinGroup.mk cycThree *
        (ProjGenLinGroup.mk (phaseGL hτ * fourierGL h3 hs * (phaseGL hτ)⁻¹))⁻¹ =
      ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk cycThree *
        ProjGenLinGroup.mk (diagTau hτ) := by
  set T := ProjGenLinGroup.mk (phaseGL hτ)
  set F := ProjGenLinGroup.mk (fourierGL h3 hs)
  set d := ProjGenLinGroup.mk (diagTau hτ)
  set c := ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)
  have R1 : F * d * F⁻¹ = c⁻¹ := mk_fourier_diagTau hτ h3 hs
  have R2 : F * c * F⁻¹ = d := mk_fourier_cycThree hτ h3 hs
  have R3 : T * d * T⁻¹ = d := mk_phase_diagTau hτ
  have R4 : T * c * T⁻¹ = d * c := mk_phase_cycThree hτ
  have R3' : T⁻¹ * d * T = d := by
    calc T⁻¹ * d * T = T⁻¹ * (T * d * T⁻¹) * T := by rw [R3]
      _ = d := by group
  have R4' : T⁻¹ * c * T = d⁻¹ * c := by
    calc T⁻¹ * c * T = d⁻¹ * ((T⁻¹ * d * T) * (T⁻¹ * c * T)) := by rw [R3']; group
      _ = d⁻¹ * (T⁻¹ * (d * c) * T) := by group
      _ = d⁻¹ * (T⁻¹ * (T * c * T⁻¹) * T) := by rw [R4]
      _ = d⁻¹ * c := by group
  rw [map_mul, map_mul, map_inv]
  calc T * F * T⁻¹ * c * (T * F * T⁻¹)⁻¹ = T * F * (T⁻¹ * c * T) * F⁻¹ * T⁻¹ := by group
    _ = T * (F * d * F⁻¹)⁻¹ * (F * c * F⁻¹) * T⁻¹ := by rw [R4']; group
    _ = (T * c * T⁻¹) * (T * d * T⁻¹) := by rw [R1, R2]; group
    _ = d * c * d := by rw [R4, R3]

end Relations

section NormalForm

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_heis_normal_form (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {y₁ y₂ g₁ z₁ : GL (Fin 3) K}
    (hy₂ : y₂ ∈ slPi π 3 (p ^ f) K) (hg₁ : g₁ ∈ glPi π 3 (p ^ f) K)
    (hz₁ : z₁ ∈ StatedScalars (Fin 3) K) (hD : g₁⁻¹ * (y₁ * z₁) * g₁ = diagTau hτ) {ζ : Kˣ}
    (hζτ : (ζ : K) = τ) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    ∃ g ∈ glPi π 3 (p ^ f) K, g⁻¹ * y₂ * g = cycThree ∧ g⁻¹ * (y₁ * z₁) * g = diagTau hτ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  set τu := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ,
    Units.val_one])
  have hζu : ζ = τu := Units.ext (by rw [hζτ, Units.val_mk0])
  set d := diagTau hτ with hd
  set c : GL (Fin 3) K := cycThree with hc
  have hcS : c ∈ slPi π 3 (p ^ f) K := cycThree_mem_slPi hπ
  set y₂' := g₁⁻¹ * y₂ * g₁ with hy₂'
  have hy₂'S : y₂' ∈ slPi π 3 (p ^ f) K := by
    have := conj_mem_slPi hπ (inv_mem hg₁) hy₂
    rwa [inv_inv] at this
  have hz₁c := commute_of_mem_statedScalars hz₁ y₂
  have hdy : d * y₂' * d⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂' := by
    rw [← hD, hy₂']
    calc g₁⁻¹ * (y₁ * z₁) * g₁ * (g₁⁻¹ * y₂ * g₁) * (g₁⁻¹ * (y₁ * z₁) * g₁)⁻¹ =
        g₁⁻¹ * (y₁ * (z₁ * y₂ * z₁⁻¹) * y₁⁻¹) * g₁ := by group
      _ = g₁⁻¹ * (y₁ * y₂ * y₁⁻¹) * g₁ := by rw [← hz₁c]; group
      _ = (g₁⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ) * y₂ * g₁ := by rw [hζ]; group
      _ = (GeneralLinearGroup.scalar (Fin 3) ζ * g₁⁻¹) * y₂ * g₁ := by rw [hsc]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ * (g₁⁻¹ * y₂ * g₁) := by group
  have hcd : c * d * c⁻¹ = GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) * d := by
    have := cycThree_pow_conj_diagTau hτ hτ0 1
    rwa [pow_one, mul_one] at this
  have hdc : d * c⁻¹ * d⁻¹ = GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) * c⁻¹ := by
    have h1 : c * d = GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) * d * c := by
      calc c * d = c * d * c⁻¹ * c := by group
        _ = _ := by rw [hcd]
    calc d * c⁻¹ * d⁻¹ = c⁻¹ * (c * d) * c⁻¹ * d⁻¹ := by group
      _ = c⁻¹ * (GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) * d * c) * c⁻¹ * d⁻¹ := by rw [h1]
      _ = c⁻¹ * GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) := by group
      _ = _ := by rw [hsc]
  have hDc : (y₂' * c⁻¹) * d = d * (y₂' * c⁻¹) := by
    have h1 : d * (y₂' * c⁻¹) * d⁻¹ = y₂' * c⁻¹ := by
      calc d * (y₂' * c⁻¹) * d⁻¹ = (d * y₂' * d⁻¹) * (d * c⁻¹ * d⁻¹) := by group
        _ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂' *
            (GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) * c⁻¹) := by rw [hdy, hdc]
        _ = GeneralLinearGroup.scalar (Fin 3) ζ * (y₂' *
            GeneralLinearGroup.scalar (Fin 3) (τu ^ 2)) * c⁻¹ := by group
        _ = GeneralLinearGroup.scalar (Fin 3) ζ * (GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) *
            y₂') * c⁻¹ := by rw [hsc]
        _ = GeneralLinearGroup.scalar (Fin 3) (ζ * τu ^ 2) * (y₂' * c⁻¹) := by
            rw [map_mul]; group
        _ = y₂' * c⁻¹ := by
            rw [hζu, ← pow_succ', hτu3, map_one, one_mul]
    calc (y₂' * c⁻¹) * d = (d * (y₂' * c⁻¹) * d⁻¹) * d := by rw [h1]
      _ = d * (y₂' * c⁻¹) := by group
  have hDmem : y₂' * c⁻¹ ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {d} :=
    Subgroup.mem_inf.mpr ⟨mul_mem hy₂'S (inv_mem hcS),
      Subgroup.mem_centralizer_singleton_iff.mpr hDc⟩
  rw [hd, centralizer_diagTau_eq hK hq hτ hτ1] at hDmem
  obtain ⟨⟨a, b⟩, hab⟩ := hDmem
  change torusHom ((a : Kˣ), (b : Kˣ)) = y₂' * c⁻¹ at hab
  set Δ : GL (Fin 3) K := diagUnits 1 (b : Kˣ) (a : Kˣ)⁻¹ with hΔ
  have hΔH : Δ ∈ glPi π 3 (p ^ f) K := diagUnits_mem_glPi hK (one_mem _) b.2 (inv_mem a.2)
  have hΔd : Δ⁻¹ * d * Δ = d := by
    have h1 : d * Δ = Δ * d := by
      rw [hd, diagTau_eq_diagUnits hτ hτ0, hΔ, diagUnits_mul, diagUnits_mul]
      congr 1 <;> exact mul_comm _ _
    calc Δ⁻¹ * d * Δ = Δ⁻¹ * (d * Δ) := by group
      _ = Δ⁻¹ * (Δ * d) := by rw [h1]
      _ = d := by group
  have hΔc : Δ⁻¹ * y₂' * Δ = c := by
    have hy : y₂' = torusHom ((a : Kˣ), (b : Kˣ)) * c := by rw [hab]; group
    have hcΔ : c * Δ * c⁻¹ = diagUnits (a : Kˣ)⁻¹ 1 (b : Kˣ) := by
      rw [hc, hΔ, cycThree_conj_diagUnits]
    have htΔ : torusHom ((a : Kˣ), (b : Kˣ)) * diagUnits (a : Kˣ)⁻¹ 1 (b : Kˣ) = Δ := by
      change diagUnits (a : Kˣ) (b : Kˣ) ((a : Kˣ) * (b : Kˣ))⁻¹ *
        diagUnits (a : Kˣ)⁻¹ 1 (b : Kˣ) = diagUnits 1 (b : Kˣ) (a : Kˣ)⁻¹
      rw [diagUnits_mul]
      congr 1
      · exact mul_inv_cancel _
      · exact mul_one _
      · rw [mul_inv, inv_mul_cancel_right]
    calc Δ⁻¹ * y₂' * Δ = Δ⁻¹ * (torusHom ((a : Kˣ), (b : Kˣ)) * (c * Δ * c⁻¹)) * c := by
          rw [hy]; group
      _ = Δ⁻¹ * Δ * c := by rw [hcΔ, htΔ]
      _ = c := by group
  refine ⟨g₁ * Δ, mul_mem hg₁ hΔH, ?_, ?_⟩
  · calc (g₁ * Δ)⁻¹ * y₂ * (g₁ * Δ) = Δ⁻¹ * y₂' * Δ := by rw [hy₂']; group
      _ = c := hΔc
  · calc (g₁ * Δ)⁻¹ * (y₁ * z₁) * (g₁ * Δ) = Δ⁻¹ * (g₁⁻¹ * (y₁ * z₁) * g₁) * Δ := by group
      _ = d := by rw [hD, hΔd]

end NormalForm

section Transitive

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {p f : ℕ}
  {π : Bool}

theorem transitive_of_normal_form (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) {x₁ x₂ : G} (hx₁ : x₁ ∈ L) (hx₂ : x₂ ∈ L)
    (he₁ : ((e ⟨x₁, hx₁⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * diagTau hτ * g⁻¹))
    (he₂ : ((e ⟨x₂, hx₂⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * cycThree * g⁻¹)) :
    ∀ x ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, x ≠ 1 →
      ∀ y ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, y ≠ 1 →
        ∃ n ∈ L ⊓ Subgroup.normalizer
          ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G), n * x * n⁻¹ = y := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have h3 := hK.three_ne_zero hq
  have hs := one_add_tau_add_sq hτ hτ1
  set F := fourierGL h3 hs with hF
  set T := phaseGL hτ with hT
  have hFS : F ∈ slPi π 3 (p ^ f) K := fourierGL_mem_slPi hK hq hτ h3 hs
  have hTH : T ∈ glPi π 3 (p ^ f) K := phaseGL_mem_glPi hK hq hτ
  have hgF : g * F * g⁻¹ ∈ slPi π 3 (p ^ f) K := conj_mem_slPi hπ hg hFS
  have hgN : g * (T * F * T⁻¹) * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    conj_mem_slPi hπ hg (conj_mem_slPi hπ hTH hFS)
  set φ : L →* ProjGenLinGroup (Fin 3) K :=
    (projImage (slPi π 3 (p ^ f) K)).subtype.comp e.toMonoidHom with hφ
  have hφinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  set X₁ : L := ⟨x₁, hx₁⟩
  set X₂ : L := ⟨x₂, hx₂⟩
  obtain ⟨N₁, hN₁⟩ : ∃ N : L, e N = projOf _ ⟨g * F * g⁻¹, hgF⟩ :=
    ⟨e.symm _, MulEquiv.apply_symm_apply _ _⟩
  obtain ⟨N₂, hN₂⟩ : ∃ N : L, e N = projOf _ ⟨g * (T * F * T⁻¹) * g⁻¹, hgN⟩ :=
    ⟨e.symm _, MulEquiv.apply_symm_apply _ _⟩
  set mg := ProjGenLinGroup.mk g
  set md := ProjGenLinGroup.mk (diagTau hτ)
  set mc := ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)
  set mF := ProjGenLinGroup.mk F
  set mN := ProjGenLinGroup.mk (T * F * T⁻¹)
  have hφ₁ : φ X₁ = mg * md * mg⁻¹ := by
    change ((e X₁ : projImage _) : ProjGenLinGroup (Fin 3) K) = _
    rw [he₁, map_mul, map_mul, map_inv]
  have hφ₂ : φ X₂ = mg * mc * mg⁻¹ := by
    change ((e X₂ : projImage _) : ProjGenLinGroup (Fin 3) K) = _
    rw [he₂, map_mul, map_mul, map_inv]
  have hφN₁ : φ N₁ = mg * mF * mg⁻¹ := by
    change ((e N₁ : projImage _) : ProjGenLinGroup (Fin 3) K) = _
    rw [hN₁, coe_projOf, map_mul, map_mul, map_inv]
  have hφN₂ : φ N₂ = mg * mN * mg⁻¹ := by
    change ((e N₂ : projImage _) : ProjGenLinGroup (Fin 3) K) = _
    rw [hN₂, coe_projOf, map_mul, map_mul, map_inv]
  have R1 : mF * md * mF⁻¹ = mc⁻¹ := mk_fourier_diagTau hτ h3 hs
  have R2 : mF * mc * mF⁻¹ = md := mk_fourier_cycThree hτ h3 hs
  have R5 : md * mc = mc * md := mk_diagTau_cycThree hτ
  have R6 : mN * md * mN⁻¹ = mc⁻¹ * md⁻¹ := mk_conjFourier_diagTau hτ h3 hs
  have R7 : mN * mc * mN⁻¹ = md * mc * md := mk_conjFourier_cycThree hτ h3 hs
  have hd3 : md ^ 3 = 1 := by rw [← map_pow, diagTau_pow_three hτ, map_one]
  have hc3 : mc ^ 3 = 1 := by rw [← map_pow, cycThree_pow_three, map_one]
  have h12 : X₁ * X₂ = X₂ * X₁ := hφinj (by
    rw [map_mul, map_mul, hφ₁, hφ₂]
    calc mg * md * mg⁻¹ * (mg * mc * mg⁻¹) = mg * (md * mc) * mg⁻¹ := by group
      _ = mg * (mc * md) * mg⁻¹ := by rw [R5]
      _ = mg * mc * mg⁻¹ * (mg * md * mg⁻¹) := by group)
  have h1 : X₁ ^ 3 = 1 := hφinj (by rw [map_pow, hφ₁, conj_pow, hd3, map_one]; group)
  have h2 : X₂ ^ 3 = 1 := hφinj (by rw [map_pow, hφ₂, conj_pow, hc3, map_one]; group)
  have hF1 : N₁ * X₁ * N₁⁻¹ = X₂⁻¹ := hφinj (by
    rw [map_mul, map_mul, map_inv, map_inv, hφN₁, hφ₁, hφ₂]
    calc mg * mF * mg⁻¹ * (mg * md * mg⁻¹) * (mg * mF * mg⁻¹)⁻¹ =
        mg * (mF * md * mF⁻¹) * mg⁻¹ := by group
      _ = (mg * mc * mg⁻¹)⁻¹ := by rw [R1]; group)
  have hF2 : N₁ * X₂ * N₁⁻¹ = X₁ := hφinj (by
    rw [map_mul, map_mul, map_inv, hφN₁, hφ₁, hφ₂]
    calc mg * mF * mg⁻¹ * (mg * mc * mg⁻¹) * (mg * mF * mg⁻¹)⁻¹ =
        mg * (mF * mc * mF⁻¹) * mg⁻¹ := by group
      _ = mg * md * mg⁻¹ := by rw [R2])
  have hN1 : N₂ * X₁ * N₂⁻¹ = X₂⁻¹ * X₁⁻¹ := hφinj (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hφN₂, hφ₁, hφ₂]
    calc mg * mN * mg⁻¹ * (mg * md * mg⁻¹) * (mg * mN * mg⁻¹)⁻¹ =
        mg * (mN * md * mN⁻¹) * mg⁻¹ := by group
      _ = (mg * mc * mg⁻¹)⁻¹ * (mg * md * mg⁻¹)⁻¹ := by rw [R6]; group)
  have hN2 : N₂ * X₂ * N₂⁻¹ = X₁ * X₂ * X₁ := hφinj (by
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, hφN₂, hφ₁, hφ₂]
    calc mg * mN * mg⁻¹ * (mg * mc * mg⁻¹) * (mg * mN * mg⁻¹)⁻¹ =
        mg * (mN * mc * mN⁻¹) * mg⁻¹ := by group
      _ = mg * md * mg⁻¹ * (mg * mc * mg⁻¹) * (mg * md * mg⁻¹) := by rw [R7]; group)
  exact transitive_of_q8 (M := L) (congrArg Subtype.val h12) (congrArg Subtype.val h1)
    (congrArg Subtype.val h2) (congrArg Subtype.val hF1) (congrArg Subtype.val hF2)
    (congrArg Subtype.val hN1) (congrArg Subtype.val hN2) N₁.2 N₂.2

theorem transitive_of_heis_pair (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {x₁ x₂ : G} (hx₁ : x₁ ∈ L) (hx₂ : x₂ ∈ L)
    {y₁ y₂ : GL (Fin 3) K}
    (he₁ : ((e ⟨x₁, hx₁⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk y₁)
    (he₂ : ((e ⟨x₂, hx₂⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk y₂)
    (h1 : Type123 π (p ^ f) K y₁ 1) (hy₂ : y₂ ∈ slPi π 3 (p ^ f) K) {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    ∀ x ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, x ≠ 1 →
      ∀ y ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, y ≠ 1 →
        ∃ n ∈ L ⊓ Subgroup.normalizer
          ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G), n * x * n⁻¹ = y := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1, z₁, hz₁, g₁, hg₁, hD⟩ := h1
  have hz₁s := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz₁
  have hmk₁ : ProjGenLinGroup.mk y₁ = ProjGenLinGroup.mk (y₁ * z₁) := by
    rw [map_mul, mk_eq_one_iff_mem_statedScalars.mpr hz₁s, mul_one]
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hζ3 : (ζ : K) ^ 3 = 1 := by
    have := pow_three_eq_one_of_conj_eq_scalar_mul hζ
    have h := congrArg Units.val this
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
  have hζ1' : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
  rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hζ3 with h | h | h
  · exact absurd h hζ1'
  · obtain ⟨g, hg, hgc, hgd⟩ := exists_heis_normal_form hK hq hτ hτ1 hy₂ hg₁ hz₁s hD h hζ
    refine transitive_of_normal_form hK hq e hτ hτ1 hg hx₁ hx₂ ?_ ?_
    · rw [he₁, hmk₁, ← hgd]
      congr 1
      group
    · rw [he₂, ← hgc]
      congr 1
      group
  ·
    have hζ' : y₁ * y₂⁻¹ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * y₂⁻¹ := by
      calc y₁ * y₂⁻¹ * y₁⁻¹ = (y₁ * y₂ * y₁⁻¹)⁻¹ := by group
        _ = (GeneralLinearGroup.scalar (Fin 3) ζ * y₂)⁻¹ := by rw [hζ]
        _ = y₂⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
        _ = _ := by rw [hsc]
    have hτζ : ((ζ⁻¹ : Kˣ) : K) = τ := by
      rw [Units.val_inv_eq_inv_val, h]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hτ])
    obtain ⟨g, hg, hgc, hgd⟩ :=
      exists_heis_normal_form hK hq hτ hτ1 (inv_mem hy₂) hg₁ hz₁s hD hτζ hζ'
    have hx₂' : x₂⁻¹ ∈ L := inv_mem hx₂
    have hsup : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂⁻¹ =
        Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := by rw [Subgroup.zpowers_inv]
    have key := transitive_of_normal_form hK hq e hτ hτ1 hg hx₁ hx₂' ?_ ?_
    · rw [hsup] at key
      exact key
    · rw [he₁, hmk₁, ← hgd]
      congr 1
      group
    · have : (⟨x₂⁻¹, hx₂'⟩ : L) = (⟨x₂, hx₂⟩ : L)⁻¹ := rfl
      rw [this, map_inv, Subgroup.coe_inv, he₂, ← hgc, ← map_inv]
      congr 1
      group

end Transitive

end CFSG.RankThree.PartTwo.Sec4
