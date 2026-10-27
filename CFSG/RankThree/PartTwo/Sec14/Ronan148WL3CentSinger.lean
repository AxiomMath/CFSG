module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentConfig
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentMat
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentQ8
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentInner
import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardMat
import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

section CharTwo

variable {K : Type} [Field K] [CharP K 2]

theorem one_add_smul_sq (t : K) (B : Matrix (Fin 3) (Fin 3) K) :
    (1 + t • B) ^ 2 = 1 + t ^ 2 • B ^ 2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hBB : t • B + t • B = 0 := by rw [← two_smul K (t • B), h2, zero_smul]
  calc (1 + t • B) ^ 2 = (1 + t • B) * (1 + t • B) := sq _
    _ = 1 + (t • B + t • B) + (t • B) * (t • B) := by
        rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul]
        abel
    _ = 1 + t ^ 2 • B ^ 2 := by rw [hBB, add_zero, smul_mul_smul_comm, sq, sq]

theorem singer_powers {A : Matrix (Fin 3) (Fin 3) K} {μ : K} (hA : A ^ 3 = μ • 1)
    (hμ : μ ^ 3 = 1) :
    (1 + A) ^ 4 = 1 + μ • A ∧ (1 + A) ^ 16 = 1 + μ ^ 2 • A ∧ (1 + A) ^ 64 = 1 + A ∧
      (1 + A) ^ 9 = A + μ ^ 2 • A ^ 2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hA4 : A ^ 4 = μ • A := by rw [pow_succ, hA, smul_mul_assoc, one_mul]
  have hA22 : (A ^ 2) ^ 2 = μ • A := by rw [← pow_mul, hA4]
  have hsq1 : ∀ B : Matrix (Fin 3) (Fin 3) K, (1 + B) ^ 2 = 1 + B ^ 2 := fun B => by
    simpa using one_add_smul_sq (1 : K) B
  have hμ5 : (μ ^ 2) ^ 2 * μ = μ ^ 2 := by
    rw [← pow_mul, ← pow_succ, show 2 * 2 + 1 = 3 + 2 from rfl, pow_add, hμ, one_mul]
  have hμ9 : ((μ ^ 2) ^ 2) ^ 2 * μ = 1 := by
    rw [← pow_mul, ← pow_mul, ← pow_succ, show 2 * 2 * 2 + 1 = 3 * 3 from rfl, pow_mul, hμ,
      one_pow]
  have h4 : (1 + A) ^ 4 = 1 + μ • A := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq1, hsq1, hA22]
  have h8 : (1 + A) ^ 8 = 1 + μ ^ 2 • A ^ 2 := by
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, h4, one_add_smul_sq]
  have h16 : (1 + A) ^ 16 = 1 + μ ^ 2 • A := by
    rw [show (16 : ℕ) = 8 * 2 from rfl, pow_mul, h8, one_add_smul_sq, hA22, smul_smul, hμ5]
  refine ⟨h4, h16, ?_, ?_⟩
  · rw [show (64 : ℕ) = 16 * 2 * 2 from rfl, pow_mul, pow_mul, h16, one_add_smul_sq,
      one_add_smul_sq, hA22, smul_smul, hμ9, one_smul]
  · rw [show (9 : ℕ) = 8 + 1 from rfl, pow_succ, h8]
    have h3 : (1 : Matrix (Fin 3) (Fin 3) K) + μ ^ 3 • 1 = 0 := by
      rw [hμ, one_smul, ← two_smul K (1 : Matrix (Fin 3) (Fin 3) K), h2, zero_smul]
    calc (1 + μ ^ 2 • A ^ 2) * (1 + A) = (1 + μ ^ 2 • (A ^ 2 * A)) + A + μ ^ 2 • A ^ 2 := by
          rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, smul_mul_assoc]
          abel
      _ = A + μ ^ 2 • A ^ 2 := by
          rw [← pow_succ, hA, smul_smul, ← pow_succ, h3, zero_add]

end CharTwo

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem mk_conj_eq_of_commute (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {β γ : MulAut (projImage (slPi π 3 (p ^ f) K))} {P Y : GL (Fin 3) K}
    (hβ : ∀ m : projImage (slPi π 3 (p ^ f) K),
      (β m : ProjGenLinGroup (Fin 3) K) = pmk P * m * (pmk P)⁻¹)
    (hγ : ∀ m : projImage (slPi π 3 (p ^ f) K),
      (γ m : ProjGenLinGroup (Fin 3) K) = pmk Y * m * (pmk Y)⁻¹)
    (h : β * γ = γ * β) : pmk (P * Y * P⁻¹) = pmk Y := by
  have := Sec13.isPerfect_projImage_slPi hK hq2
  have hw : (Y * P)⁻¹ * (P * Y) ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_comm_mod hK hq fun s hs => ?_
    rw [← mk_eq_one_iff_mem_statedScalars]
    have h1 := congrArg (fun δ : MulAut (projImage (slPi π 3 (p ^ f) K)) =>
      ((δ (projOf _ ⟨s, hs⟩) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K)) h
    simp only [MulAut.mul_apply, hβ, hγ, coe_projOf] at h1
    simp only [map_mul, map_inv]
    calc (pmk Y * pmk P)⁻¹ * (pmk P * pmk Y) * pmk s * ((pmk Y * pmk P)⁻¹ * (pmk P * pmk Y))⁻¹ *
          (pmk s)⁻¹ =
        (pmk Y * pmk P)⁻¹ * (pmk P * (pmk Y * pmk s * (pmk Y)⁻¹) * (pmk P)⁻¹) *
          (pmk Y * pmk P) * (pmk s)⁻¹ := by group
      _ = (pmk Y * pmk P)⁻¹ * (pmk Y * (pmk P * pmk s * (pmk P)⁻¹) * (pmk Y)⁻¹) *
          (pmk Y * pmk P) * (pmk s)⁻¹ := by rw [h1]
      _ = 1 := by group
  rw [← mk_eq_one_iff_mem_statedScalars] at hw
  have h2 : pmk (P * Y) = pmk (Y * P) := by
    rw [map_mul, map_inv] at hw
    exact (inv_mul_eq_one.mp hw).symm
  rw [map_mul, map_mul, map_inv, ← map_mul, h2, map_mul, mul_inv_cancel_right]

variable {ι : Type*}

theorem diagUnits_mul_cycThree_cube (a b c : Kˣ) :
    ((diagUnits a b c * cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      ((a * b * c : Kˣ) : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [Units.val_mul, coe_diagUnits_eq, coe_cycThree]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> ring

theorem diagTau_conj_cycThree {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) :
    diagTau hτ * cycThree * (diagTau hτ)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * cycThree := by
  rw [diagTau_eq_diagUnits hτ hτ0, Sec12.KS128Move.diagUnits_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_diagUnits_eq, coe_diagUnits_eq,
    coe_cycThree, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have h3 : (τ ^ 2)⁻¹ = τ := inv_eq_of_mul_eq_one_right (by linear_combination hτ)
  have h4 : τ⁻¹ = τ ^ 2 := inv_eq_of_mul_eq_one_right (by linear_combination hτ)
  have h1 : τ * (τ ^ 2)⁻¹ = τ ^ 2 := by rw [h3, ← sq]
  have h2 : τ ^ 2 * τ⁻¹ = τ := by
    rw [h4, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_add, hτ, one_mul, pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h2, h3, Units.val_inv_eq_inv_val]

theorem CentConfig.mem_zpowers_of_conj_of_commute (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {α : ι → MulAut (projImage (slPi π 3 (p ^ f) K))}
    {e₀ : projImage (slPi π 3 (p ^ f) K)} (hc : CentConfig π p f K α e₀)
    {β : MulAut (projImage (slPi π 3 (p ^ f) K))} (hβ3 : β ^ 3 = 1)
    (hβc : ∀ y, β * α y = α y * β) {u : projImage (slPi π 3 (p ^ f) K)}
    (hu : β = MulAut.conj u) : u ∈ Subgroup.zpowers e₀ := by
  refine hc.hF3 u ?_ fun y => ?_
  · apply eq_one_of_conj_eq_one hK hq hq2
    rw [map_pow, ← hu, hβ3]
  · have h1 : MulAut.conj (α y u) = MulAut.conj u := by
      rw [mulAut_conj_apply_eq, ← hu, ← hβc y, mul_inv_cancel_right]
    have h2 : α y u * u⁻¹ = 1 :=
      eq_one_of_conj_eq_one hK hq hq2 (by rw [map_mul, map_inv, h1, mul_inv_cancel])
    exact mul_inv_eq_one.mp h2

theorem mk_monomial_ne_mk_diagUnits (a b c a' b' c' : Kˣ) :
    pmk (diagUnits a b c * cycThree : GL (Fin 3) K) ≠ pmk (diagUnits a' b' c') := by
  intro h
  apply RonanK432.L3Hard.mk_cycThree_ne_mk_diagUnits (a⁻¹ * a') (b⁻¹ * b') (c⁻¹ * c')
  have h1 := congrArg (fun m => (pmk (diagUnits a b c))⁻¹ * m) h
  simp only [map_mul, inv_mul_cancel_left] at h1
  rw [h1, ← map_inv, ← map_mul, Sec12.KS128Move.diagUnits_inv, diagUnits_mul]

theorem pow_three_eq_one_of_card_four [Finite K] (hK : Nat.card K = 4) {t : K} (ht : t ≠ 0) :
    t ^ 3 = 1 := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one t ht
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem CentConfig.false_of_singer [CharP K 2] (hK : PiField true 2 2 K)
    {α : ι → MulAut (projImage (slPi true 3 (2 ^ 2) K))}
    {e₀ : projImage (slPi true 3 (2 ^ 2) K)} (hc : CentConfig true 2 2 K α e₀) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ))
    (hpgl : ∀ x, IsPGLAct true 2 2 K (α x)) {γ : MulAut (projImage (slPi true 3 (2 ^ 2) K))}
    (hγ3 : γ ^ 3 = 1) (hγc : ∀ x, γ * α x = α x * γ) {a b c : Kˣ}
    (hγ : ∀ m : projImage (slPi true 3 (2 ^ 2) K), (γ m : ProjGenLinGroup (Fin 3) K) =
      pmk (diagUnits a b c * cycThree) * (m : ProjGenLinGroup (Fin 3) K) *
        (pmk (diagUnits a b c * cycThree))⁻¹) : False := by
  have hq : ModThree true (2 ^ 2) := rfl
  have hq2 : 2 < 2 ^ 2 := by norm_num
  have := hK.finite
  have hcard : Nat.card K = 4 := hK.card
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨Y, hY⟩ : ∃ Y : GL (Fin 3) K, Y = diagUnits a b c * cycThree := ⟨_, rfl⟩
  simp only [← hY] at hγ
  set μ : Kˣ := a * b * c with hμ
  have hYm : (Y : Matrix (Fin 3) (Fin 3) K) = !![0, 0, (a : K); (b : K), 0, 0; 0, (c : K), 0] := by
    rw [hY, Units.val_mul, coe_diagUnits_eq, coe_cycThree]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hY3 := diagUnits_mul_cycThree_cube a b c
  rw [← hμ, ← hY] at hY3
  have hμ3 : (μ : K) ^ 3 = 1 := pow_three_eq_one_of_card_four hcard μ.ne_zero
  have he₀3 : e₀ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, he₀, ← map_pow, diagTau_pow_three hτ, map_one]; rfl)
  by_cases hμ1 : (μ : K) = 1
  ·
    have hYs : Y ∈ slPi true 3 (2 ^ 2) K := by
      rw [mem_slPi_true, hYm, det_fin_three]
      simp [Matrix.vecHead, Matrix.vecTail]
      have : ((a * b * c : Kˣ) : K) = 1 := hμ1
      rw [Units.val_mul, Units.val_mul] at this
      linear_combination this
    have hu := hc.mem_zpowers_of_conj_of_commute hK hq hq2 hγ3 hγc
      (u := ⟨pmk Y, Y, hYs, rfl⟩) (by
        ext m
        rw [hγ, MulAut.conj_apply]
        rfl)
    have hd3 : pmk (diagTau hτ) ^ 3 = 1 := by rw [← map_pow, diagTau_pow_three hτ, map_one]
    have hu' : pmk Y ∈ Subgroup.zpowers (pmk (diagTau hτ)) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
        have := congrArg Subtype.val hk
        rwa [Subgroup.coe_zpow, he₀] at this⟩
    rw [diagTau_eq_diagUnits hτ hτ0] at hd3 hu'
    rw [hY] at hu'
    rcases RonanK432.mem_zpowers_cases_of_pow_three hd3 hu' with h | h | h
    · exact mk_monomial_ne_mk_diagUnits a b c 1 1 1 (by rw [h, Sec12.KS128Move.diagUnits_one,
        map_one])
    · exact mk_monomial_ne_mk_diagUnits a b c _ _ _ h
    · exact mk_monomial_ne_mk_diagUnits a b c _ _ _ (by
        rw [h, ← map_inv, Sec12.KS128Move.diagUnits_inv])
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨A, hA⟩ : ∃ A, A = (Y : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  have hAm : A = !![0, 0, (a : K); (b : K), 0, 0; 0, (c : K), 0] := hA.trans hYm
  have hA3 : A ^ 3 = (μ : K) • 1 := hA ▸ hY3
  obtain ⟨h4, h16, h64, h9⟩ := singer_powers hA3 hμ3
  have hdet1 : (1 + A).det = 1 + (μ : K) := by
    rw [hAm, hμ, Units.val_mul, Units.val_mul, det_fin_three]
    simp [Matrix.vecHead, Matrix.vecTail]
  have hne : (1 : K) + μ ≠ 0 := fun h => hμ1 (by linear_combination h - h2)
  set U : GL (Fin 3) K := GeneralLinearGroup.mkOfDetNeZero (1 + A) (by rw [hdet1]; exact hne)
    with hUdef
  have hU : (U : Matrix (Fin 3) (Fin 3) K) = 1 + A := GeneralLinearGroup.val_mkOfDetNeZero _ _
  set z := U ^ 9 with hzdef
  have hz : (z : Matrix (Fin 3) (Fin 3) K) = A + (μ : K) ^ 2 • A ^ 2 := by
    rw [hzdef, Units.val_pow_eq_pow_val, hU, h9]
  have hU63 : U ^ 63 = 1 := by
    have h : U ^ 63 * U = U := Units.ext (by
      rw [← pow_succ, Units.val_pow_eq_pow_val, hU, h64])
    exact mul_eq_right.mp h
  have hz7 : z ^ 7 = 1 := by rw [hzdef, ← pow_mul]; exact hU63
  have hzs : z ∈ slPi true 3 (2 ^ 2) K := by
    rw [mem_slPi_true, hzdef, Units.val_pow_eq_pow_val, det_pow, hU, hdet1,
      show 9 = 3 * 3 from rfl, pow_mul, pow_three_eq_one_of_card_four hcard hne, one_pow]
  set w : projImage (slPi true 3 (2 ^ 2) K) := projOf _ ⟨z, hzs⟩ with hwdef
  have hw : (w : ProjGenLinGroup (Fin 3) K) = pmk z := coe_projOf _ _
  have hw7 : w ^ 7 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hw, ← map_pow, hz7, map_one]; rfl)
  have hμu3 : μ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hμ3)
  have hμu1 : μ ≠ 1 := fun h => hμ1 (by rw [h, Units.val_one])
  have hconjU : ∀ (P : GL (Fin 3) K) (ν : Kˣ),
      P * Y * P⁻¹ = GeneralLinearGroup.scalar (Fin 3) ν * Y →
      ∃ i < 3, ν = μ ^ i ∧ P * U * P⁻¹ = U ^ (4 ^ i) := by
    intro P ν hP
    have hν3 : ν ^ 3 = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact pow_three_eq_one_of_card_four hcard ν.ne_zero)
    obtain ⟨i, hi, rfl⟩ := eq_pow_of_pow_three hμu3 hμu1 hν3
    refine ⟨i, hi, rfl, Units.ext ?_⟩
    have hPA : (P : Matrix (Fin 3) (Fin 3) K) * A * ((P⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((μ ^ i : Kˣ) : K) • A := by
      have h := congrArg Units.val hP
      rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] at h
      rw [hA]
      exact h
    rw [Units.val_mul, Units.val_mul, hU, Units.val_pow_eq_pow_val, hU, mul_add, add_mul,
      mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, hPA, Units.val_pow_eq_pow_val]
    interval_cases i
    · simp
    · rw [show (4 : ℕ) ^ 1 = 4 from rfl, h4, pow_one]
    · rw [show (4 : ℕ) ^ 2 = 16 from rfl, h16]
  have hinv : ∀ y, ∀ v ∈ Subgroup.zpowers w, α y v ∈ Subgroup.zpowers w := by
    intro y v hv
    obtain ⟨P, -, hPy⟩ := hpgl y
    have hcomm := mk_conj_eq_of_commute hK hq hq2 hPy hγ (hγc y).symm
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hcomm
    have hPY : P * Y * P⁻¹ = GeneralLinearGroup.scalar (Fin 3) u⁻¹ * Y := by
      calc P * Y * P⁻¹ = P * Y * P⁻¹ * GeneralLinearGroup.scalar (Fin 3) u *
            GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by
            rw [mul_assoc (P * Y * P⁻¹), ← map_mul, mul_inv_cancel, map_one, mul_one]
        _ = GeneralLinearGroup.scalar (Fin 3) u⁻¹ * Y := by
            rw [hu]
            exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u⁻¹ Y).eq
    obtain ⟨i, -, -, hPU⟩ := hconjU P u⁻¹ hPY
    have hyw : α y w = w ^ (4 ^ i) := Subtype.ext (by
      rw [hPy, hw, Subgroup.coe_pow, hw, ← map_inv, ← map_mul, ← map_mul, ← map_pow, hzdef,
        ← _root_.conj_pow, hPU, ← pow_mul, ← pow_mul, mul_comm])
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [map_zpow, hyw, ← zpow_natCast, ← _root_.zpow_mul]
    exact Subgroup.zpow_mem_zpowers w _
  have hW3 : ¬ 3 ∣ Nat.card (Subgroup.zpowers w) := by
    rw [Nat.card_zpowers]
    intro h3
    have h7 := orderOf_dvd_of_pow_eq_one hw7
    have := Nat.le_of_dvd (by norm_num) (dvd_trans h3 h7)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h7 with h | h <;> rw [h] at h3 <;>
      norm_num at h3
  obtain ⟨x₀, hx₀⟩ := hc.conj_e
  have hfix := congrArg Subtype.val (hc.hV _ hW3 hinv x₀ w (Subgroup.mem_zpowers w))
  have hdY : diagTau hτ * Y * (diagTau hτ)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * Y := by
    rw [hY, diagTau_eq_diagUnits hτ hτ0]
    calc diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1 * (diagUnits a b c * cycThree) *
          (diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1)⁻¹ =
        diagUnits a b c * (diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1 * cycThree *
          (diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1)⁻¹) := by
          rw [← mul_assoc, Sec12.KS128Move.diagUnits_comm]
          group
      _ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (diagUnits a b c * cycThree) := by
          rw [← diagTau_eq_diagUnits hτ hτ0, diagTau_conj_cycThree hτ hτ0, ← mul_assoc,
            (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar _ (diagUnits a b c)).eq, mul_assoc]
  obtain ⟨i, hi, hνi, hdU⟩ := hconjU _ _ hdY
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hτ1
    have := congrArg Units.val hνi
    rwa [pow_zero, Units.val_one, Units.val_mk0] at this
  rw [hx₀, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, he₀, hw,
    ← map_inv, ← map_mul, ← map_mul, hzdef, ← _root_.conj_pow, hdU, ← pow_mul, mul_comm,
    pow_mul, map_pow] at hfix
  have hz7' : pmk z ^ 7 = 1 := by rw [← map_pow, hz7, map_one]
  have hz1 : pmk z = 1 := by
    have hord7 := orderOf_dvd_of_pow_eq_one hz7'
    have hordi : orderOf (pmk z) ∣ 4 ^ i - 1 := by
      apply orderOf_dvd_of_pow_eq_one
      have h1 : pmk z ^ (4 ^ i - 1) * pmk z = pmk z := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))]
        exact hfix
      exact mul_eq_right.mp h1
    have hcop : Nat.Coprime 7 (4 ^ i - 1) := by
      rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl <;> norm_num
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord7 hordi)
  obtain ⟨s', hs'⟩ := mk_eq_one_iff_mem_statedScalars.mp hz1
  have h01 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1) hs'
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h01
  rw [hz, hAm] at h01
  simp [sq, Matrix.mul_apply, Fin.sum_univ_three] at h01

theorem exists_monomial_two_sq (a b c : Kˣ) :
    ∃ a' b' c' : Kˣ, (diagUnits a b c * cycThree ^ 2) ^ 2 = diagUnits a' b' c' * cycThree := by
  obtain ⟨x, y, z, h⟩ := exists_cycThree_pow_conj_diagUnits 2 a b c
  refine ⟨a * x, b * y, c * z, ?_⟩
  have hc4 : (cycThree : GL (Fin 3) K) ^ 4 = cycThree := by
    rw [show 4 = 3 + 1 from rfl, pow_add, RonanK432.L3Hard.cycThree_cube, one_mul, pow_one]
  calc (diagUnits a b c * cycThree ^ 2) ^ 2 =
      diagUnits a b c * (cycThree ^ 2 * diagUnits a b c * (cycThree ^ 2)⁻¹) * cycThree ^ 4 := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        group
    _ = diagUnits (a * x) (b * y) (c * z) * cycThree := by
        rw [h, hc4, diagUnits_mul]

theorem CentConfig.false_of_L34 [CharP K 2] (hK : PiField true 2 2 K)
    {α : ι → MulAut (projImage (slPi true 3 (2 ^ 2) K))}
    {e₀ : projImage (slPi true 3 (2 ^ 2) K)} (hc : CentConfig true 2 2 K α e₀) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ)) :
    False := by
  have hq : ModThree true (2 ^ 2) := rfl
  have hpgl : ∀ x, IsPGLAct true 2 2 K (α x) := fun x =>
    (hc.dich x).resolve_right (by
      rintro ⟨f₀, hf, -⟩
      omega)
  have hmono : ∀ x, ∃ (a b c : Kˣ) (k : ℕ), k < 3 ∧ ∀ m : projImage (slPi true 3 (2 ^ 2) K),
      (α x m : ProjGenLinGroup (Fin 3) K) = pmk (diagUnits a b c * cycThree ^ k) *
        (m : ProjGenLinGroup (Fin 3) K) * (pmk (diagUnits a b c * cycThree ^ k))⁻¹ := by
    intro x
    obtain ⟨y, -, hyx⟩ := hpgl x
    obtain ⟨c, hc'⟩ := exists_conj_eq_scalar_mul hyx (hc.fix x) he₀
    obtain ⟨a, b, c', k, hk, rfl⟩ := monomial_of_conj_diagTau hτ hτ1 hc'
    exact ⟨a, b, c', k, hk, hyx⟩
  by_cases hnt : ∃ (x : ι) (a b c : Kˣ) (k : ℕ), 1 ≤ k ∧ k < 3 ∧
      ∀ m : projImage (slPi true 3 (2 ^ 2) K),
      (α x m : ProjGenLinGroup (Fin 3) K) = pmk (diagUnits a b c * cycThree ^ k) *
        (m : ProjGenLinGroup (Fin 3) K) * (pmk (diagUnits a b c * cycThree ^ k))⁻¹
  · obtain ⟨x, a, b, c, k, hk1, hk3, hx⟩ := hnt
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl
    · exact hc.false_of_singer hK hτ hτ1 he₀ hpgl (hc.pow_three x) (fun y => hc.comm x y)
        (a := a) (b := b) (c := c) (by simpa using hx)
    · obtain ⟨a', b', c', h2⟩ := exists_monomial_two_sq a b c
      refine hc.false_of_singer hK hτ hτ1 he₀ hpgl (γ := α x ^ 2) ?_
        (fun y => (Commute.pow_left (hc.comm x y) 2).eq) (a := a') (b := b') (c := c') ?_
      · rw [← pow_mul, mul_comm, pow_mul, hc.pow_three x, one_pow]
      · intro m
        rw [pow_two (α x), MulAut.mul_apply, hx, hx, ← h2, map_pow]
        simp only [pow_two]
        group
  · refine hc.false_of_rootGroup hK hq hτ hτ1 he₀ fun x => ?_
    obtain ⟨a, b, c, k, hk, hx⟩ := hmono x
    have hk0 : k = 0 := by
      by_contra h
      exact hnt ⟨x, a, b, c, k, by omega, hk, hx⟩
    subst hk0
    exact ⟨a, b, c, by simpa using hx⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
