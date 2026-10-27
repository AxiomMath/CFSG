module

public import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofLin
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjFieldB
public import CFSG.Quasithin.Background.C41PfI
import CFSG.Dihedral.PrimeClassPartition
import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofSub
import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofCentGen
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.RankThree.PartTwo.Sec16.Item166Res5ProofNoE4
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofGen
import CFSG.Quasithin.Vol2.F134LieOddMatrix
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.TwoWeightData
import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofU
import CFSG.Quasithin.Vol2.Ch11SecQ9aL3A

public section

namespace CFSG.RankThree.PartTwo.KFacts.PSLThreeHessian

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec14.Item148OneRepair
open CFSG.RankThree.PartTwo.Sec16.ProofKSL3Two CFSG.RankThree.PartTwo.Sec16.ProofNoE4
open CFSG.Quasithin CFSG.Quasithin.F134.LieOdd CFSG.ComponentClassification
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open Matrix

variable {K : Type} [Field K] {ω : K}

theorem omega_pow_three (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

theorem omega_ne_zero (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  rintro rfl
  norm_num at hω

theorem omega_sq_ne_one (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) : ω ^ 2 ≠ 1 := by
  intro h
  apply hω1
  have h3 := omega_pow_three hω
  calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by field_simp [omega_ne_zero hω]
    _ = 1 := by rw [h3, h, inv_one, mul_one]

@[expose] def omegaUnit (hω : ω ^ 2 + ω + 1 = 0) : Kˣ :=
  Units.mk0 ω (omega_ne_zero hω)

@[simp]
theorem coe_omegaUnit (hω : ω ^ 2 + ω + 1 = 0) : (omegaUnit hω : K) = ω := rfl

theorem omegaUnit_pow_three (hω : ω ^ 2 + ω + 1 = 0) : omegaUnit hω ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, coe_omegaUnit, omega_pow_three hω, Units.val_one])

@[expose] noncomputable def hessD (hω : ω ^ 2 + ω + 1 = 0) : SpecialLinearGroup (Fin 3) K :=
  diagSL148 (omega_pow_three hω)

@[expose] noncomputable def hessP : SpecialLinearGroup (Fin 3) K := cycleSL148

@[expose] noncomputable def hessDGL (hω : ω ^ 2 + ω + 1 = 0) : GL (Fin 3) K :=
  C41Pf.diagUnits (![1, omegaUnit hω, omegaUnit hω ^ 2] : Fin 3 → Kˣ)

@[expose] noncomputable def hessPGL : GL (Fin 3) K := cycThree

@[expose] noncomputable def hessE9 (hω : ω ^ 2 + ω + 1 = 0) : Subgroup (projectiveSL 3 K) :=
  Subgroup.closure ({proj 3 K (hessD hω), proj 3 K (hessP (K := K))} : Set _)

theorem hessD_pow_three (hω : ω ^ 2 + ω + 1 = 0) : hessD hω ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact diagOmega_pow_three148 (omega_pow_three hω)

theorem hessP_pow_three : hessP (K := K) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact cycle_pow_three148

@[simp]
theorem coe_hessD (hω : ω ^ 2 + ω + 1 = 0) :
    (hessD hω : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![1, ω, ω ^ 2] := rfl

@[simp]
theorem coe_hessP : (hessP (K := K) : Matrix (Fin 3) (Fin 3) K) = cycle148 := rfl

@[simp]
theorem coe_hessDGL (hω : ω ^ 2 + ω + 1 = 0) :
    (hessDGL hω : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![1, ω, ω ^ 2] := by
  rw [hessDGL, C41Pf.coe_diagUnits]
  congr 1
  funext i
  fin_cases i <;> simp [coe_omegaUnit]

@[simp]
theorem coe_hessPGL :
    (hessPGL (K := K) : Matrix (Fin 3) (Fin 3) K) = cycle148 :=
  coe_cycThree

theorem toGL_hessD (hω : ω ^ 2 + ω + 1 = 0) :
    SpecialLinearGroup.toGL (hessD hω) = hessDGL hω := by
  apply Units.ext
  rw [coe_hessDGL]
  rfl

theorem toGL_hessP : SpecialLinearGroup.toGL (hessP (K := K)) = hessPGL (K := K) := by
  apply Units.ext
  rw [coe_hessPGL]
  rfl

theorem hessP_conj_hessD (hω : ω ^ 2 + ω + 1 = 0) :
    hessPGL (K := K) * hessDGL hω * (hessPGL (K := K))⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) * hessDGL hω := by
  apply Units.ext
  simp only [Units.val_mul, hessPGL, hessDGL, C41Pf.coe_diagUnits,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hdiag : (fun i => ↑(![1, omegaUnit hω, omegaUnit hω ^ 2] i) : Fin 3 → K) =
      ![1, ω, ω ^ 2] := by
    funext i
    fin_cases i <;> simp [coe_omegaUnit]
  rw [hdiag]
  simp only [Units.val_pow_eq_pow_val, coe_omegaUnit]
  rw [cyc_mul_diagonal_mul_inv, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_omegaUnit, omega_pow_three hω]
  · rw [← pow_succ, omega_pow_three hω]
  · rw [show ω ^ 2 * ω ^ 2 = ω ^ 4 by ring, show (4 : ℕ) = 3 + 1 by norm_num, pow_add,
      omega_pow_three hω, one_mul]
    rw [pow_one]

section Elementary

variable (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)

private theorem pow_fin_add_of_pow_three {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1)
    (i j : Fin 3) : x ^ ((i + j : Fin 3) : ℕ) = x ^ (i : ℕ) * x ^ (j : ℕ) := by
  rw [← pow_add, pow_eq_pow_mod ((i + j : Fin 3) : ℕ) hx,
    pow_eq_pow_mod ((i : ℕ) + (j : ℕ)) hx]
  congr 1
  fin_cases i <;> fin_cases j <;> decide

private theorem pow_fin_neg_of_pow_three {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1)
    (i : Fin 3) : (x ^ (i : ℕ))⁻¹ = x ^ ((-i : Fin 3) : ℕ) := by
  apply inv_eq_of_mul_eq_one_right
  have h := pow_fin_add_of_pow_three hx i (-i)
  rw [add_neg_cancel] at h
  simpa using h.symm

private theorem pow_fin_eq_one_of_pow_three {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1)
    (hx1 : x ≠ 1) {i : Fin 3} (hi : x ^ (i : ℕ) = 1) : i = 0 := by
  fin_cases i
  · rfl
  · exact absurd (by simpa using hi) hx1
  · have h : x = 1 := by
      calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx, hi]; group
    exact absurd h hx1

theorem mem_hessE9_iff (x : projectiveSL 3 K) :
    x ∈ hessE9 hω ↔ ∃ i j : Fin 3,
      x = (proj 3 K (hessD hω)) ^ (i : ℕ) * (proj 3 K (hessP (K := K))) ^ (j : ℕ) := by
  set a := proj 3 K (hessD hω) with ha
  set b := proj 3 K (hessP (K := K)) with hb
  have hab : Commute a b := proj_diagSL_mul_cycleSL148 (omega_pow_three hω)
  have ha3 : a ^ 3 = 1 := proj_diagSL_pow_three148 (omega_pow_three hω)
  have hb3 : b ^ 3 = 1 := proj_cycleSL_pow_three148 (K := K)
  have hpowA : ∀ i j : Fin 3, a ^ ((i + j : Fin 3) : ℕ) = a ^ (i : ℕ) * a ^ (j : ℕ) :=
    fun i j => pow_fin_add_of_pow_three ha3 i j
  have hpowB : ∀ i j : Fin 3, b ^ ((i + j : Fin 3) : ℕ) = b ^ (i : ℕ) * b ^ (j : ℕ) :=
    fun i j => pow_fin_add_of_pow_three hb3 i j
  have hnegA : ∀ i : Fin 3, (a ^ (i : ℕ))⁻¹ = a ^ ((-i : Fin 3) : ℕ) :=
    fun i => pow_fin_neg_of_pow_three ha3 i
  have hnegB : ∀ i : Fin 3, (b ^ (i : ℕ))⁻¹ = b ^ ((-i : Fin 3) : ℕ) :=
    fun i => pow_fin_neg_of_pow_three hb3 i
  constructor
  · intro hx
    let S : Subgroup (projectiveSL 3 K) :=
      { carrier := {x | ∃ i j : Fin 3, x = a ^ (i : ℕ) * b ^ (j : ℕ)}
        mul_mem' := by
          rintro x y ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
          refine ⟨i + k, j + l, ?_⟩
          rw [hpowA i k, hpowB j l]
          calc (a ^ (i : ℕ) * b ^ (j : ℕ)) * (a ^ (k : ℕ) * b ^ (l : ℕ))
              = a ^ (i : ℕ) * (b ^ (j : ℕ) * (a ^ (k : ℕ) * b ^ (l : ℕ))) := by group
            _ = a ^ (i : ℕ) * ((b ^ (j : ℕ) * a ^ (k : ℕ)) * b ^ (l : ℕ)) := by group
            _ = a ^ (i : ℕ) * ((a ^ (k : ℕ) * b ^ (j : ℕ)) * b ^ (l : ℕ)) := by
                rw [(hab.symm.pow_pow (j : ℕ) (k : ℕ)).eq]
            _ = (a ^ (i : ℕ) * a ^ (k : ℕ)) * (b ^ (j : ℕ) * b ^ (l : ℕ)) := by group
        one_mem' := ⟨0, 0, by simp⟩
        inv_mem' := by
          rintro x ⟨i, j, rfl⟩
          refine ⟨-i, -j, ?_⟩
          rw [_root_.mul_inv_rev, hnegA, hnegB]
          simpa [hnegA, hnegB] using
            ((hab.symm.pow_pow (j : ℕ) (i : ℕ)).inv_left.inv_right).eq }
    have hle : hessE9 hω ≤ S := by
      rw [hessE9]
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨1, 0, by simp [ha.symm]⟩
      · exact ⟨0, 1, by simp [hb.symm]⟩
    exact hle hx
  · rintro ⟨i, j, rfl⟩
    have ha_mem : a ∈ hessE9 hω := by
      rw [hessE9, ha]
      exact Subgroup.subset_closure (by simp)
    have hb_mem : b ∈ hessE9 hω := by
      rw [hessE9, hb]
      exact Subgroup.subset_closure (by simp)
    exact mul_mem (pow_mem ha_mem _) (pow_mem hb_mem _)

theorem hessE9_isElemAbelian : CFSG.Assembly.IsElemAbelian 3 (hessE9 hω) := by
  set a := proj 3 K (hessD hω) with ha
  set b := proj 3 K (hessP (K := K)) with hb
  have hab : Commute a b := proj_diagSL_mul_cycleSL148 (omega_pow_three hω)
  have ha3 : a ^ 3 = 1 := proj_diagSL_pow_three148 (omega_pow_three hω)
  have hb3 : b ^ 3 = 1 := proj_cycleSL_pow_three148 (K := K)
  have hpair : ({a, b} : Set (projectiveSL 3 K)).Pairwise Commute := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  refine ⟨Subgroup.isMulCommutative_closure hpair, ?_⟩
  intro x hx
  exact CFSG.GroupTheory.TwoWeights.closure_pow_eq_one (S := ({a, b} : Set (projectiveSL 3 K))) (n := 3)
    (by
      intro s hs
      rcases hs with rfl | rfl
      · exact ha3
      · exact hb3)
    (by
      intro s hs t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
      · rfl
      · exact hab.eq
      · exact hab.symm.eq
      · rfl)
    x hx

theorem hessE9_pow_injective (hω1 : ω ≠ 1) {i i' j j' : Fin 3}
    (h : (proj 3 K (hessD hω)) ^ (i : ℕ) * (proj 3 K (hessP (K := K))) ^ (j : ℕ) =
      (proj 3 K (hessD hω)) ^ (i' : ℕ) * (proj 3 K (hessP (K := K))) ^ (j' : ℕ)) :
    i = i' ∧ j = j' := by
  set a := proj 3 K (hessD hω) with ha
  set b := proj 3 K (hessP (K := K)) with hb
  have hab : Commute a b := proj_diagSL_mul_cycleSL148 (omega_pow_three hω)
  have ha3 : a ^ 3 = 1 := proj_diagSL_pow_three148 (omega_pow_three hω)
  have hb3 : b ^ 3 = 1 := proj_cycleSL_pow_three148 (K := K)
  have ha1 : a ≠ 1 := proj_diagSL_ne_one148 (omega_pow_three hω) hω1
  have hb1 : b ≠ 1 := by
    simpa [hb, hessP] using proj_cycleSL_ne_pow148 (omega_pow_three hω) 0
  have hnegA : ∀ i : Fin 3, (a ^ (i : ℕ))⁻¹ = a ^ ((-i : Fin 3) : ℕ) :=
    fun i => pow_fin_neg_of_pow_three ha3 i
  have hnegB : ∀ i : Fin 3, (b ^ (i : ℕ))⁻¹ = b ^ ((-i : Fin 3) : ℕ) :=
    fun i => pow_fin_neg_of_pow_three hb3 i
  have hpowA : ∀ i j : Fin 3, a ^ ((i + j : Fin 3) : ℕ) = a ^ (i : ℕ) * a ^ (j : ℕ) :=
    fun i j => pow_fin_add_of_pow_three ha3 i j
  have hpowB : ∀ i j : Fin 3, b ^ ((i + j : Fin 3) : ℕ) = b ^ (i : ℕ) * b ^ (j : ℕ) :=
    fun i j => pow_fin_add_of_pow_three hb3 i j
  have h1 : a ^ (((-i') + i : Fin 3) : ℕ) = b ^ ((j' + (-j) : Fin 3) : ℕ) := by
    have h2 : a ^ (i : ℕ) = a ^ (i' : ℕ) * (b ^ (j' : ℕ) * (b ^ (j : ℕ))⁻¹) := by
      calc a ^ (i : ℕ) = a ^ (i : ℕ) * b ^ (j : ℕ) * (b ^ (j : ℕ))⁻¹ := by group
        _ = a ^ (i' : ℕ) * b ^ (j' : ℕ) * (b ^ (j : ℕ))⁻¹ := by rw [h]
        _ = a ^ (i' : ℕ) * (b ^ (j' : ℕ) * (b ^ (j : ℕ))⁻¹) := by group
    calc a ^ (((-i') + i : Fin 3) : ℕ)
        = a ^ ((-i' : Fin 3) : ℕ) * a ^ (i : ℕ) := hpowA (-i') i
      _ = a ^ ((-i' : Fin 3) : ℕ) * (a ^ (i' : ℕ) * (b ^ (j' : ℕ) * (b ^ (j : ℕ))⁻¹)) := by
          rw [h2]
      _ = (a ^ ((-i' : Fin 3) : ℕ) * a ^ (i' : ℕ)) *
            (b ^ (j' : ℕ) * (b ^ (j : ℕ))⁻¹) := by group
      _ = b ^ (j' : ℕ) * (b ^ (j : ℕ))⁻¹ := by
          rw [show a ^ ((-i' : Fin 3) : ℕ) * a ^ (i' : ℕ) = 1 by
            rw [← hpowA (-i') i']
            rw [show ((-i' + i' : Fin 3) : ℕ) = 0 by simp]
            exact pow_zero a, one_mul]
      _ = b ^ ((j' + (-j) : Fin 3) : ℕ) := by
          rw [hnegB j, ← hpowB j' (-j)]
  set l : Fin 3 := j' + (-j) with hl
  have h1' : a ^ (((-i') + i : Fin 3) : ℕ) = b ^ (l : ℕ) := by
    simpa [hl] using h1
  have hl0 : l = 0 := by
    by_contra hl0
    have hlv : l.val = 1 ∨ l.val = 2 := by
      have := l.isLt
      omega
    rcases hlv with h1 | h2
    · have hl1 : l = 1 := Fin.ext (by simpa using h1)
      exfalso
      have hb_eq : b = a ^ (((-i') + i : Fin 3) : ℕ) := by
        simpa [hl1] using h1'.symm
      exact proj_cycleSL_ne_pow148 (omega_pow_three hω)
        (((-i') + i : Fin 3) : ℕ) hb_eq
    · have hl2 : l = 2 := Fin.ext (by simpa using h2)
      exfalso
      have hb2inv : b = (b ^ 2)⁻¹ := by
        calc b = (b ^ 2)⁻¹ * b ^ 2 * b := by rw [inv_mul_cancel, one_mul]
          _ = (b ^ 2)⁻¹ * (b ^ 2 * b) := by group
          _ = (b ^ 2)⁻¹ := by
              rw [show b ^ 2 * b = 1 by rw [← pow_succ, show (2 : ℕ) + 1 = 3 by norm_num, hb3],
                mul_one]
      have hb2_eq : b ^ 2 = b ^ (l : ℕ) := by rw [hl2]; norm_num
      have hb_eq : b = a ^ ((-(-i' + i) : Fin 3) : ℕ) := by
        calc b = (b ^ 2)⁻¹ := hb2inv
          _ = (b ^ (l : ℕ))⁻¹ := by rw [hb2_eq]
          _ = (a ^ (((-i') + i : Fin 3) : ℕ))⁻¹ := by rw [← h1']
          _ = a ^ ((-(-i' + i) : Fin 3) : ℕ) := hnegA _
      exact proj_cycleSL_ne_pow148 (omega_pow_three hω)
        ((-(-i' + i) : Fin 3) : ℕ) hb_eq
  have hk0 : (-i') + i = 0 := by
    have hb0 : b ^ (l : ℕ) = 1 := by rw [hl0]; simp
    have ha0 : a ^ (((-i') + i : Fin 3) : ℕ) = 1 := by rw [h1', hb0]
    exact pow_fin_eq_one_of_pow_three ha3 ha1 ha0
  constructor
  · exact (neg_add_eq_zero.mp hk0).symm
  · exact (add_neg_eq_zero.mp (by simpa [hl] using hl0)).symm

theorem card_hessE9 (hω1 : ω ≠ 1) : Nat.card (hessE9 hω) = 9 := by
  set a := proj 3 K (hessD hω) with ha
  set b := proj 3 K (hessP (K := K)) with hb
  have ha_mem : a ∈ hessE9 hω := by
    rw [hessE9, ha]
    exact Subgroup.subset_closure (by simp)
  have hb_mem : b ∈ hessE9 hω := by
    rw [hessE9, hb]
    exact Subgroup.subset_closure (by simp)
  let f : Fin 3 × Fin 3 → hessE9 hω := fun p =>
    ⟨a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ), mul_mem (pow_mem ha_mem _) (pow_mem hb_mem _)⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    have hval : a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ) = a ^ (q.1 : ℕ) * b ^ (q.2 : ℕ) :=
      congrArg Subtype.val hpq
    obtain ⟨h1, h2⟩ := hessE9_pow_injective (hω := hω) hω1 hval
    exact Prod.ext h1 h2
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨i, j, hij⟩ := (mem_hessE9_iff (hω := hω) x).mp x.2
    exact ⟨(i, j), Subtype.ext hij.symm⟩
  have e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  rw [← Nat.card_congr e]
  norm_num

end Elementary

section MatrixNormalizer

variable (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)

theorem injective_hessDiag (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) : Function.Injective (![1, ω, ω ^ 2] : Fin 3 → K) := by
  intro i j hij
  have hω3 := omega_pow_three hω
  have hω2 : ω ^ 2 ≠ 1 := omega_sq_ne_one hω hω1
  have hω_ne_sq : ω ≠ ω ^ 2 := by
    intro h
    apply hω2
    calc ω ^ 2 = ω * ω := by ring
      _ = ω ^ 2 * ω := by rw [← h]
      _ = 1 := by rw [← pow_succ, hω3]
  have h1_ne_sq : (1 : K) ≠ ω ^ 2 := fun h => hω2 h.symm
  fin_cases i <;> fin_cases j <;> simp_all [hω1, hω2, hω_ne_sq, h1_ne_sq]

theorem det_hessDGL : (hessDGL hω : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [coe_hessDGL, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, one_mul, coe_omegaUnit]
  rw [mul_comm, ← pow_succ, omega_pow_three hω]

theorem det_hessDGL_unit : GeneralLinearGroup.det (hessDGL hω) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_hessDGL hω, Units.val_one]

theorem scalar_pow_three_of_conj_hessD {g : GL (Fin 3) K} {ζ : Kˣ}
    (h : g * hessDGL hω * g⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ζ * hessDGL hω) : ζ ^ 3 = 1 := by
  have hdetScalar : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) ζ) = ζ ^ 3 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, det_scalar_eq, Units.val_pow_eq_pow_val]
  have hdet := congrArg (fun x : GL (Fin 3) K => GeneralLinearGroup.det x) h
  rw [map_mul, map_mul, map_inv, map_mul, det_hessDGL_unit hω, mul_one, hdetScalar] at hdet
  simpa using hdet.symm

theorem hessP_sq_conj_hessD :
    hessPGL (K := K) ^ 2 * hessDGL hω * (hessPGL (K := K) ^ 2)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) * hessDGL hω := by
  have hP := hessP_conj_hessD (K := K) hω
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hsq : (hessPGL (K := K) ^ 2)⁻¹ =
      (hessPGL (K := K))⁻¹ * (hessPGL (K := K))⁻¹ := by
    rw [pow_two, _root_.mul_inv_rev]
  calc hessPGL (K := K) ^ 2 * hessDGL hω * (hessPGL (K := K) ^ 2)⁻¹
      = hessPGL (K := K) *
          (hessPGL (K := K) * hessDGL hω * (hessPGL (K := K))⁻¹) *
          (hessPGL (K := K))⁻¹ := by
          rw [pow_two, _root_.mul_inv_rev]
          group
    _ = hessPGL (K := K) *
          (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) * hessDGL hω) *
          (hessPGL (K := K))⁻¹ := by rw [hP]
    _ = (hessPGL (K := K) * GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2)) *
          hessDGL hω * (hessPGL (K := K))⁻¹ := by group
    _ = (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) * hessPGL (K := K)) *
          hessDGL hω * (hessPGL (K := K))⁻¹ := by
          rw [hsc (omegaUnit hω ^ 2) (hessPGL (K := K))]
    _ = GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) *
          (hessPGL (K := K) * hessDGL hω * (hessPGL (K := K))⁻¹) := by group
    _ = GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) *
          (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) * hessDGL hω) := by rw [hP]
    _ = GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) * hessDGL hω := by
          rw [← mul_assoc, ← map_mul]
          congr 2
          rw [← pow_add, show (2 : ℕ) + 2 = 3 + 1 by norm_num, pow_add,
            omegaUnit_pow_three hω, one_mul, pow_one]

theorem exists_diagUnits_eq_of_isDiag {h : GL (Fin 3) K}
    (hdiag : ∀ i j, i ≠ j → (h : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    ∃ v : Fin 3 → Kˣ, h = C41Pf.diagUnits v := by
  have hmat : (h : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal (fun i => h i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]
  have hprod : (∏ i, (h : Matrix (Fin 3) (Fin 3) K) i i) ≠ 0 := by
    have hdet := h.det_ne_zero
    rw [hmat, Matrix.det_diagonal] at hdet
    exact hdet
  let v : Fin 3 → Kˣ := fun i =>
    Units.mk0 ((h : Matrix (Fin 3) (Fin 3) K) i i)
      (Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i))
  refine ⟨v, ?_⟩
  apply Units.ext
  rw [C41Pf.coe_diagUnits, hmat]
  rfl

theorem exists_pow_mul_diag_of_conj_diag (hω1 : ω ≠ 1) {g : GL (Fin 3) K} {ζ : Kˣ}
    (h : g * hessDGL hω * g⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ζ * hessDGL hω) :
    ∃ (k : ℕ) (v : Fin 3 → Kˣ), g = hessPGL (K := K) ^ k * C41Pf.diagUnits v := by
  have hζ3 : ζ ^ 3 = 1 := scalar_pow_three_of_conj_hessD (K := K) hω h
  have hζ3' : (ζ : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have hP := hessP_conj_hessD (K := K) hω
  have hP2 := hessP_sq_conj_hessD (K := K) hω
  have hP3 : hessPGL (K := K) ^ 3 = 1 := by
    rw [← toGL_hessP, ← map_pow, hessP_pow_three, map_one]
  have hdiag_of_comm : ∀ h' : GL (Fin 3) K,
      h' * hessDGL hω * h'⁻¹ = hessDGL hω →
      ∃ v : Fin 3 → Kˣ, h' = C41Pf.diagUnits v := by
    intro h' hh'
    have hcomm : h' * hessDGL hω = hessDGL hω * h' := by
      calc h' * hessDGL hω = (h' * hessDGL hω * h'⁻¹) * h' := by group
        _ = hessDGL hω * h' := by rw [hh']
    have hcomm_mat : (h' : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal ![1, ω, ω ^ 2] =
        Matrix.diagonal ![1, ω, ω ^ 2] * (h' : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hcomm
      simpa [coe_hessDGL] using this
    have hIs : IsDiag3 (h' : Matrix (Fin 3) (Fin 3) K) :=
      isDiag3_of_commute_diagonal (injective_hessDiag (K := K) hω hω1) hcomm_mat
    exact exists_diagUnits_eq_of_isDiag (K := K) hIs
  rcases CFSG.RankThree.PartTwo.Sec16.KS165UProof.cube_root_cases hω hζ3' with hζ | hζ | hζ
  ·
    have hζu : ζ = 1 := Units.ext hζ
    obtain ⟨v, hv⟩ := hdiag_of_comm g (by rw [hζu] at h; simpa using h)
    exact ⟨0, v, by rw [pow_zero, one_mul, hv]⟩
  ·
    have hζu : ζ = omegaUnit hω := Units.ext (by rw [coe_omegaUnit]; exact hζ)
    have hcomm_scalar : hessPGL (K := K) *
        (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) * hessDGL hω) *
        (hessPGL (K := K))⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) *
          (hessPGL (K := K) * hessDGL hω * (hessPGL (K := K))⁻¹) := by
      calc hessPGL (K := K) *
            (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) * hessDGL hω) *
            (hessPGL (K := K))⁻¹
          = (hessPGL (K := K) * GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω)) *
              hessDGL hω * (hessPGL (K := K))⁻¹ := by group
        _ = (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) * hessPGL (K := K)) *
              hessDGL hω * (hessPGL (K := K))⁻¹ := by
              rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (omegaUnit hω)
                (hessPGL (K := K))).eq]
        _ = GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) *
              (hessPGL (K := K) * hessDGL hω * (hessPGL (K := K))⁻¹) := by group
    have hprod : omegaUnit hω * omegaUnit hω ^ 2 = 1 := by
      rw [mul_comm, ← pow_succ, show (2 : ℕ) + 1 = 3 by norm_num, omegaUnit_pow_three hω]
    have hh : (hessPGL (K := K) * g) * hessDGL hω * (hessPGL (K := K) * g)⁻¹ =
        hessDGL hω := by
      calc (hessPGL (K := K) * g) * hessDGL hω * (hessPGL (K := K) * g)⁻¹
          = hessPGL (K := K) * (g * hessDGL hω * g⁻¹) * (hessPGL (K := K))⁻¹ := by group
        _ = hessPGL (K := K) *
              (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) * hessDGL hω) *
              (hessPGL (K := K))⁻¹ := by rw [h, hζu]
        _ = _ := hcomm_scalar
        _ = GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) *
              (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) * hessDGL hω) := by rw [hP]
        _ = hessDGL hω := by
              rw [← mul_assoc, ← map_mul, hprod, map_one, one_mul]
    obtain ⟨v, hv⟩ := hdiag_of_comm (hessPGL (K := K) * g) hh
    refine ⟨2, v, ?_⟩
    calc g = (hessPGL (K := K))⁻¹ * (hessPGL (K := K) * g) := by group
      _ = hessPGL (K := K) ^ 2 * C41Pf.diagUnits v := by
          rw [hv]
          rw [show (hessPGL (K := K))⁻¹ = hessPGL (K := K) ^ 2 by
            calc (hessPGL (K := K))⁻¹ = (hessPGL (K := K))⁻¹ * 1 := by rw [mul_one]
              _ = (hessPGL (K := K))⁻¹ * (hessPGL (K := K)) ^ 3 := by rw [hP3]
              _ = (hessPGL (K := K)) ^ 2 := by group]
  ·
    have hζu : ζ = omegaUnit hω ^ 2 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, coe_omegaUnit]
      exact hζ)
    have hcomm_scalar : hessPGL (K := K) ^ 2 *
        (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) * hessDGL hω) *
        (hessPGL (K := K) ^ 2)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) *
          (hessPGL (K := K) ^ 2 * hessDGL hω * (hessPGL (K := K) ^ 2)⁻¹) := by
      have hsq : (hessPGL (K := K) ^ 2)⁻¹ =
          (hessPGL (K := K))⁻¹ * (hessPGL (K := K))⁻¹ := by
        rw [pow_two, _root_.mul_inv_rev]
      calc hessPGL (K := K) ^ 2 *
            (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) * hessDGL hω) *
            (hessPGL (K := K) ^ 2)⁻¹
          = (hessPGL (K := K) ^ 2 *
              GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2)) *
              hessDGL hω * (hessPGL (K := K) ^ 2)⁻¹ := by group
        _ = (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) * hessPGL (K := K) ^ 2) *
              hessDGL hω * (hessPGL (K := K) ^ 2)⁻¹ := by
              rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (omegaUnit hω ^ 2)
                (hessPGL (K := K) ^ 2)).eq]
        _ = GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) *
              (hessPGL (K := K) ^ 2 * hessDGL hω * (hessPGL (K := K) ^ 2)⁻¹) := by group
    have hprod : omegaUnit hω ^ 2 * omegaUnit hω = 1 := by
      rw [← pow_succ, show (2 : ℕ) + 1 = 3 by norm_num, omegaUnit_pow_three hω]
    have hh : (hessPGL (K := K) ^ 2 * g) * hessDGL hω *
        (hessPGL (K := K) ^ 2 * g)⁻¹ = hessDGL hω := by
      calc (hessPGL (K := K) ^ 2 * g) * hessDGL hω *
            (hessPGL (K := K) ^ 2 * g)⁻¹
          = hessPGL (K := K) ^ 2 * (g * hessDGL hω * g⁻¹) *
              (hessPGL (K := K) ^ 2)⁻¹ := by group
        _ = hessPGL (K := K) ^ 2 *
              (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) * hessDGL hω) *
              (hessPGL (K := K) ^ 2)⁻¹ := by rw [h, hζu]
        _ = _ := hcomm_scalar
        _ = GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω ^ 2) *
              (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) * hessDGL hω) := by rw [hP2]
        _ = hessDGL hω := by
              rw [← mul_assoc, ← map_mul, hprod, map_one, one_mul]
    obtain ⟨v, hv⟩ := hdiag_of_comm (hessPGL (K := K) ^ 2 * g) hh
    refine ⟨1, v, ?_⟩
    calc g = (hessPGL (K := K) ^ 2)⁻¹ * (hessPGL (K := K) ^ 2 * g) := by group
      _ = hessPGL (K := K) ^ 1 * C41Pf.diagUnits v := by
          rw [hv]
          rw [show (hessPGL (K := K) ^ 2)⁻¹ = hessPGL (K := K) ^ 1 by
            calc (hessPGL (K := K) ^ 2)⁻¹ = (hessPGL (K := K) ^ 2)⁻¹ * 1 := by rw [mul_one]
              _ = (hessPGL (K := K) ^ 2)⁻¹ * (hessPGL (K := K)) ^ 3 := by rw [hP3]
              _ = hessPGL (K := K) ^ 1 := by group]

theorem diagUnits_vec_eq (v : Fin 3 → Kˣ) :
    C41Pf.diagUnits v = diagUnits (v 0) (v 1) (v 2) := by
  apply Units.ext
  rw [C41Pf.coe_diagUnits, coe_diagUnits_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem hessDGL_eq_diagUnits :
    hessDGL hω = diagUnits 1 (omegaUnit hω) (omegaUnit hω ^ 2) := by
  apply Units.ext
  rw [coe_hessDGL, coe_diagUnits_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem scalar_eq_diagUnits (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) c = diagUnits c c c := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagUnits_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_scalar_pow_of_diag_conj_cycle {v : Fin 3 → Kˣ} {ζ : Kˣ}
    (h : C41Pf.diagUnits v * hessPGL (K := K) * (C41Pf.diagUnits v)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ζ * hessPGL (K := K)) :
    ∃ (c : Kˣ) (j : ℕ), C41Pf.diagUnits v =
      GeneralLinearGroup.scalar (Fin 3) c * hessDGL hω ^ j := by
  set a := v 0 with ha
  set b := v 1 with hb
  set c := v 2 with hc
  have hD_vec : C41Pf.diagUnits v = diagUnits a b c := by
    rw [diagUnits_vec_eq, ha, hb, hc]
  have h' : diagUnits a b c * hessPGL (K := K) * (diagUnits a b c)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ζ * hessPGL (K := K) := by
    simpa [hD_vec] using h
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hDP : diagUnits a b c * hessPGL (K := K) =
      GeneralLinearGroup.scalar (Fin 3) ζ * (hessPGL (K := K) * diagUnits a b c) := by
    calc diagUnits a b c * hessPGL (K := K)
        = (diagUnits a b c * hessPGL (K := K) * (diagUnits a b c)⁻¹) *
            diagUnits a b c := by group
      _ = (GeneralLinearGroup.scalar (Fin 3) ζ * hessPGL (K := K)) * diagUnits a b c := by
          rw [h']
      _ = GeneralLinearGroup.scalar (Fin 3) ζ * (hessPGL (K := K) * diagUnits a b c) := by
          group
  have hPD : hessPGL (K := K) * diagUnits a b c = diagUnits c a b * hessPGL (K := K) := by
    calc hessPGL (K := K) * diagUnits a b c
        = (hessPGL (K := K) * diagUnits a b c * (hessPGL (K := K))⁻¹) *
            hessPGL (K := K) := by group
      _ = diagUnits c a b * hessPGL (K := K) := by
          rw [hessPGL, cycThree_conj_diagUnits]
  have hD : diagUnits a b c = GeneralLinearGroup.scalar (Fin 3) ζ * diagUnits c a b := by
    calc diagUnits a b c
        = (diagUnits a b c * hessPGL (K := K)) * (hessPGL (K := K))⁻¹ := by group
      _ = (GeneralLinearGroup.scalar (Fin 3) ζ *
            (hessPGL (K := K) * diagUnits a b c)) * (hessPGL (K := K))⁻¹ := by rw [hDP]
      _ = (GeneralLinearGroup.scalar (Fin 3) ζ *
            (diagUnits c a b * hessPGL (K := K))) * (hessPGL (K := K))⁻¹ := by rw [hPD]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ * diagUnits c a b := by
          group
  have haζ : a = ζ * c := by
    have h00 := congrFun (congrFun (congrArg
      (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hD) 0) 0
    simp [diagUnits, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply] at h00
    exact Units.ext h00
  have hbζ : b = ζ * a := by
    have h11 := congrFun (congrFun (congrArg
      (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hD) 1) 1
    simp [diagUnits, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply] at h11
    exact Units.ext h11
  have hcζ : c = ζ * b := by
    have h22 := congrFun (congrFun (congrArg
      (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hD) 2) 2
    simp [diagUnits, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply] at h22
    exact Units.ext h22
  have hζ3 : ζ ^ 3 = 1 := by
    have h3 : a = ζ ^ 3 * a := by
      calc a = ζ * c := haζ
        _ = ζ * (ζ * b) := by rw [hcζ]
        _ = ζ * (ζ * (ζ * a)) := by rw [hbζ]
        _ = ζ ^ 3 * a := by
            rw [show ζ ^ 3 = ζ * ζ * ζ by rw [pow_succ, pow_two]]
            group
    have h4 : ζ ^ 3 * a = 1 * a := by rw [← h3, one_mul]
    exact mul_right_cancel h4
  have hζ3' : (ζ : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have hb' : b = a * ζ := by rw [hbζ, mul_comm]
  have hc' : c = a * ζ ^ 2 := by
    rw [hcζ, hbζ, pow_two]
    ac_rfl
  have hDa : diagUnits a b c =
      GeneralLinearGroup.scalar (Fin 3) a * diagUnits 1 ζ (ζ ^ 2) := by
    calc diagUnits a b c = diagUnits a (a * ζ) (a * ζ ^ 2) := by rw [hb', hc']
      _ = diagUnits a a a * diagUnits 1 ζ (ζ ^ 2) := by rw [diagUnits_mul]; simp
      _ = GeneralLinearGroup.scalar (Fin 3) a * diagUnits 1 ζ (ζ ^ 2) := by
          rw [← scalar_eq_diagUnits]
  rcases CFSG.RankThree.PartTwo.Sec16.KS165UProof.cube_root_cases hω hζ3' with hζ | hζ | hζ
  ·
    have hζu : ζ = 1 := Units.ext hζ
    refine ⟨a, 0, ?_⟩
    rw [hζu] at hDa
    rw [hD_vec, hDa, pow_zero]
    congr 1
    apply Units.ext
    rw [coe_diagUnits_eq, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  ·
    have hζu : ζ = omegaUnit hω := Units.ext (by rw [coe_omegaUnit]; exact hζ)
    refine ⟨a, 1, ?_⟩
    rw [hD_vec, hDa, hζu, pow_one, ← hessDGL_eq_diagUnits]
  ·
    have hζu : ζ = omegaUnit hω ^ 2 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, coe_omegaUnit]
      exact hζ)
    refine ⟨a, 2, ?_⟩
    rw [hD_vec, hDa, hζu, hessDGL_eq_diagUnits, diagUnits_pow]
    simp

theorem exists_scalar_pow_mul_diag_pow_of_normalizer (hω1 : ω ≠ 1) {g : GL (Fin 3) K}
    {ζ₁ ζ₂ : Kˣ}
    (h₁ : g * hessDGL hω * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ₁ * hessDGL hω)
    (h₂ : g * hessPGL (K := K) * g⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ζ₂ * hessPGL (K := K)) :
    ∃ (c : Kˣ) (k j : ℕ), g = GeneralLinearGroup.scalar (Fin 3) c *
      (hessPGL (K := K) ^ k * hessDGL hω ^ j) := by
  obtain ⟨k, v, hg⟩ := exists_pow_mul_diag_of_conj_diag (K := K) hω hω1 h₁
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hD : C41Pf.diagUnits v * hessPGL (K := K) * (C41Pf.diagUnits v)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ζ₂ * hessPGL (K := K) := by
    have h2' := h₂
    rw [hg] at h2'
    calc C41Pf.diagUnits v * hessPGL (K := K) * (C41Pf.diagUnits v)⁻¹
        = (hessPGL (K := K) ^ k)⁻¹ *
            ((hessPGL (K := K) ^ k * C41Pf.diagUnits v) * hessPGL (K := K) *
              (hessPGL (K := K) ^ k * C41Pf.diagUnits v)⁻¹) *
            hessPGL (K := K) ^ k := by group
      _ = (hessPGL (K := K) ^ k)⁻¹ *
            (GeneralLinearGroup.scalar (Fin 3) ζ₂ * hessPGL (K := K)) *
            hessPGL (K := K) ^ k := by rw [h2']
      _ = GeneralLinearGroup.scalar (Fin 3) ζ₂ *
            ((hessPGL (K := K) ^ k)⁻¹ * hessPGL (K := K) * hessPGL (K := K) ^ k) := by
          calc (hessPGL (K := K) ^ k)⁻¹ *
                (GeneralLinearGroup.scalar (Fin 3) ζ₂ * hessPGL (K := K)) *
                hessPGL (K := K) ^ k
              = ((hessPGL (K := K) ^ k)⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ₂) *
                  hessPGL (K := K) * hessPGL (K := K) ^ k := by group
            _ = (GeneralLinearGroup.scalar (Fin 3) ζ₂ *
                  (hessPGL (K := K) ^ k)⁻¹) * hessPGL (K := K) *
                  hessPGL (K := K) ^ k := by
                  rw [hsc ζ₂ ((hessPGL (K := K) ^ k)⁻¹)]
            _ = GeneralLinearGroup.scalar (Fin 3) ζ₂ *
                  ((hessPGL (K := K) ^ k)⁻¹ * hessPGL (K := K) *
                    hessPGL (K := K) ^ k) := by group
      _ = GeneralLinearGroup.scalar (Fin 3) ζ₂ * hessPGL (K := K) := by
          rw [show (hessPGL (K := K) ^ k)⁻¹ * hessPGL (K := K) *
            hessPGL (K := K) ^ k = hessPGL (K := K) by group]
  obtain ⟨c, j, hv⟩ := exists_scalar_pow_of_diag_conj_cycle (K := K) hω hD
  refine ⟨c, k, j, ?_⟩
  calc g = hessPGL (K := K) ^ k * C41Pf.diagUnits v := hg
    _ = hessPGL (K := K) ^ k *
          (GeneralLinearGroup.scalar (Fin 3) c * hessDGL hω ^ j) := by rw [hv]
    _ = GeneralLinearGroup.scalar (Fin 3) c *
          (hessPGL (K := K) ^ k * hessDGL hω ^ j) := by
          calc hessPGL (K := K) ^ k *
                (GeneralLinearGroup.scalar (Fin 3) c * hessDGL hω ^ j)
              = (hessPGL (K := K) ^ k * GeneralLinearGroup.scalar (Fin 3) c) *
                  hessDGL hω ^ j := by group
            _ = (GeneralLinearGroup.scalar (Fin 3) c * hessPGL (K := K) ^ k) *
                  hessDGL hω ^ j := by rw [hsc c (hessPGL (K := K) ^ k)]
            _ = GeneralLinearGroup.scalar (Fin 3) c *
                  (hessPGL (K := K) ^ k * hessDGL hω ^ j) := by group

theorem hessD_mul_hessP :
    hessDGL hω * hessPGL (K := K) =
      GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) *
        (hessPGL (K := K) * hessDGL hω) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_hessDGL, coe_hessPGL,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  simpa [diagOmega148] using diagOmega_mul_cycle148 (omega_pow_three hω)

theorem hessD_commutator_hessP :
    hessDGL hω * hessPGL (K := K) * (hessDGL hω)⁻¹ * (hessPGL (K := K))⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) := by
  have h := hessD_mul_hessP (K := K) hω
  calc hessDGL hω * hessPGL (K := K) * (hessDGL hω)⁻¹ * (hessPGL (K := K))⁻¹
      = (GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) *
          (hessPGL (K := K) * hessDGL hω)) * (hessDGL hω)⁻¹ *
          (hessPGL (K := K))⁻¹ := by rw [h]
    _ = GeneralLinearGroup.scalar (Fin 3) (omegaUnit hω) := by group

section Hurwitz

variable (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)

theorem dualAut_proj_hessD :
    dualAut 3 K (proj 3 K (hessD hω)) = proj 3 K ((hessD hω)⁻¹) := by
  rw [dualAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv, coe_hessD]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Matrix.transpose_apply]

theorem dualAut_proj_hessP :
    dualAut 3 K (proj 3 K (hessP (K := K))) = proj 3 K (hessP (K := K)) := by
  rw [dualAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv, coe_hessP]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycle148]

theorem fieldAut_proj_hessD_of_eq (σ : K ≃+* K) (hσω : σ ω = ω) :
    fieldAut 3 K σ (proj 3 K (hessD hω)) = proj 3 K (hessD hω) := by
  rw [hessD]
  exact fieldAut_proj_diagSL148 (omega_pow_three hω) hσω

theorem fieldAut_proj_hessD_of_sq (σ : K ≃+* K) (hσω : σ ω = ω ^ 2) :
    fieldAut 3 K σ (proj 3 K (hessD hω)) = proj 3 K ((hessD hω)⁻¹) := by
  have hsq : hessD hω ^ 2 = (hessD hω)⁻¹ := by
    calc hessD hω ^ 2 = hessD hω ^ 2 * (hessD hω * (hessD hω)⁻¹) := by group
      _ = hessD hω ^ 3 * (hessD hω)⁻¹ := by group
      _ = (hessD hω)⁻¹ := by rw [hessD_pow_three hω, one_mul]
  rw [← hsq, hessD, fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSL148, diagOmega148, hσω, omega_pow_three hω, Matrix.diagonal_pow]

theorem hessD_commutator_hessP_SL :
    ((hessD hω * hessP (K := K) * (hessD hω)⁻¹ * (hessP (K := K))⁻¹ :
        SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) (omegaUnit hω : K) := by
  have hGL := hessD_commutator_hessP (K := K) hω
  have hmap : ((hessD hω * hessP (K := K) * (hessD hω)⁻¹ * (hessP (K := K))⁻¹ :
      SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((hessDGL hω * hessPGL (K := K) * (hessDGL hω)⁻¹ * (hessPGL (K := K))⁻¹ :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    change ((SpecialLinearGroup.toGL (hessD hω * hessP (K := K) * (hessD hω)⁻¹ *
      (hessP (K := K))⁻¹) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, toGL_hessD, toGL_hessP]
  rw [hmap, hGL]
  simp [Matrix.GeneralLinearGroup.coe_scalar]

theorem fieldAut_mul_dualAut_fixes_hessD (σ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1)
    (hσω : σ ω = ω ^ 2 ^ ε) :
    (fieldAut 3 K σ * dualAut 3 K ^ ε) (proj 3 K (hessD hω)) =
      proj 3 K (hessD hω) := by
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · simp only [pow_zero, MulAut.mul_apply, MulAut.one_apply]
    exact fieldAut_proj_hessD_of_eq (K := K) hω σ (by simpa using hσω)
  · simp only [pow_one, MulAut.mul_apply]
    rw [dualAut_proj_hessD (K := K) hω]
    have h := fieldAut_proj_hessD_of_sq (K := K) hω σ (by simpa using hσω)
    calc (fieldAut 3 K σ) ((proj 3 K) ((hessD hω)⁻¹))
        = ((fieldAut 3 K σ) ((proj 3 K) (hessD hω)))⁻¹ := by simp only [map_inv]
      _ = ((proj 3 K) ((hessD hω)⁻¹))⁻¹ := by rw [h]
      _ = (proj 3 K) (hessD hω) := by rw [map_inv, inv_inv]

theorem fieldAut_mul_dualAut_fixes_hessP (σ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1) :
    (fieldAut 3 K σ * dualAut 3 K ^ ε) (proj 3 K (hessP (K := K))) =
      proj 3 K (hessP (K := K)) := by
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · simp only [pow_zero, MulAut.mul_apply, MulAut.one_apply]
    exact fieldAut_proj_cycleSL148 (K := K) σ
  · simp only [pow_one, MulAut.mul_apply]
    rw [dualAut_proj_hessP (K := K)]
    change (fieldAut 3 K σ) (proj 3 K (cycleSL148 (K := K))) =
      proj 3 K (cycleSL148 (K := K))
    exact fieldAut_proj_cycleSL148 (K := K) σ

theorem exists_scalar_of_conjAut_proj_eq {A : GL (Fin 3) K}
    {g : SpecialLinearGroup (Fin 3) K}
    (h : conjAut 3 K A (proj 3 K g) = proj 3 K g) :
    ∃ ζ : Kˣ, A * SpecialLinearGroup.toGL g * A⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ζ * SpecialLinearGroup.toGL g := by
  set sl := CatalogueBHigherLinearAction.slConjugation 3 K A g with hsl
  have hconj : proj 3 K sl = proj 3 K g := by
    simpa [hsl, conjAut_proj] using h
  obtain ⟨c, hc, hcmat⟩ :=
    mem_scalars.mp (proj_eq_proj_iff.mp hconj.symm)
  have hw_eq : g⁻¹ * sl = scalarElement c hc :=
    Subtype.ext (by rw [hcmat, coe_scalarElement])
  have hsl_eq : sl = g * scalarElement c hc := by
    calc sl = g * (g⁻¹ * sl) := by group
      _ = g * scalarElement c hc := by rw [hw_eq]
  have hsc : SpecialLinearGroup.toGL (scalarElement c hc) =
      GeneralLinearGroup.scalar (Fin 3) c := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_scalarElement,
      Matrix.GeneralLinearGroup.coe_scalar]
  refine ⟨c, ?_⟩
  calc A * SpecialLinearGroup.toGL g * A⁻¹
      = SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation 3 K A g) := by
        rw [CatalogueBHigherLinearAction.toGL_slConjugation]
    _ = SpecialLinearGroup.toGL (g * scalarElement c hc) := by
        change SpecialLinearGroup.toGL sl = SpecialLinearGroup.toGL (g * scalarElement c hc)
        rw [hsl_eq]
    _ = SpecialLinearGroup.toGL g * GeneralLinearGroup.scalar (Fin 3) c := by
        rw [map_mul, hsc]
    _ = GeneralLinearGroup.scalar (Fin 3) c * SpecialLinearGroup.toGL g := by
        rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c
          (SpecialLinearGroup.toGL g)).eq]

theorem automorphisms_fixing_hessE9 [Finite K] (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (α : MulAut (projectiveSL 3 K))
    (hαd : α (proj 3 K (hessD hω)) = proj 3 K (hessD hω))
    (hαP : α (proj 3 K (hessP (K := K))) = proj 3 K (hessP (K := K))) :
    ∃ b ∈ hessE9 hω, ∃ (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧ σ ω = ω ^ 2 ^ ε ∧
      α = MulAut.conj b * (fieldAut 3 K σ * dualAut 3 K ^ ε) := by
  obtain ⟨A, σ, ε, hε, hαgen⟩ :=
    (automorphism_generation (K := K) (n := 3) (by norm_num)).2 α
  have hd_mem : proj 3 K (hessD hω) ∈ hessE9 hω := by
    rw [hessE9]
    exact Subgroup.subset_closure (by simp)
  have hP_mem : proj 3 K (hessP (K := K)) ∈ hessE9 hω := by
    rw [hessE9]
    exact Subgroup.subset_closure (by simp)
  have hfix : ∀ e ∈ hessE9 hω,
      (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) e = e := by
    intro e he
    obtain ⟨i, j, rfl⟩ := (mem_hessE9_iff (hω := hω) e).mp he
    rw [← hαgen, map_mul, map_pow, map_pow, hαd, hαP]
  have hζ : Units.map (σ : K →* K) ((omegaUnit hω) ^ ((-1 : ℤ) ^ ε)) =
      omegaUnit hω :=
    map_zeta_of_fix (E := hessE9 hω) (g₁ := hessD hω) (g₂ := hessP (K := K))
      hd_mem hP_mem (hessD_commutator_hessP_SL (K := K) hω) A σ hε hfix
  have hσω : σ ω = ω ^ 2 ^ ε := by
    rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
    · have h := congrArg (fun u : Kˣ => (u : K)) hζ
      simpa using h
    · have h := congrArg (fun u : Kˣ => (u : K)) hζ
      have hpow : (omegaUnit hω) ^ ((-1 : ℤ) ^ 1) = (omegaUnit hω)⁻¹ := by
        rw [show ((-1 : ℤ) ^ 1) = -1 by norm_num, _root_.zpow_neg_one]
      rw [hpow] at h
      simp only [Units.coe_map, Units.val_inv_eq_inv_val, coe_omegaUnit] at h
      have h' : σ ω = (ω : K)⁻¹ := by
        apply inv_eq_iff_eq_inv.mp
        simpa using h
      have hωinv : (ω : K)⁻¹ = ω ^ 2 := by
        apply inv_eq_of_mul_eq_one_right
        calc ω * ω ^ 2 = ω ^ 3 := by ring
          _ = 1 := omega_pow_three hω
      rw [h', hωinv]
      norm_num
  have hβd : (fieldAut 3 K σ * dualAut 3 K ^ ε) (proj 3 K (hessD hω)) =
      proj 3 K (hessD hω) :=
    fieldAut_mul_dualAut_fixes_hessD (K := K) hω σ hε hσω
  have hβP : (fieldAut 3 K σ * dualAut 3 K ^ ε) (proj 3 K (hessP (K := K))) =
      proj 3 K (hessP (K := K)) :=
    fieldAut_mul_dualAut_fixes_hessP (K := K) σ hε
  have hAd : conjAut 3 K A (proj 3 K (hessD hω)) = proj 3 K (hessD hω) := by
    have hβd' : fieldAut 3 K σ ((dualAut 3 K ^ ε) (proj 3 K (hessD hω))) =
        proj 3 K (hessD hω) := by
      simpa only [MulAut.mul_apply] using hβd
    have := hαd
    rw [hαgen] at this
    simp only [MulAut.mul_apply] at this
    rw [hβd'] at this
    exact this
  have hAP : conjAut 3 K A (proj 3 K (hessP (K := K))) =
      proj 3 K (hessP (K := K)) := by
    have hβP' : fieldAut 3 K σ ((dualAut 3 K ^ ε) (proj 3 K (hessP (K := K)))) =
        proj 3 K (hessP (K := K)) := by
      simpa only [MulAut.mul_apply] using hβP
    have := hαP
    rw [hαgen] at this
    simp only [MulAut.mul_apply] at this
    rw [hβP'] at this
    exact this
  obtain ⟨ζ₁, hA₁⟩ := exists_scalar_of_conjAut_proj_eq (K := K) hAd
  obtain ⟨ζ₂, hA₂⟩ := exists_scalar_of_conjAut_proj_eq (K := K) hAP
  have hA₁' : A * hessDGL hω * A⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ζ₁ * hessDGL hω := by
    simpa [toGL_hessD] using hA₁
  have hA₂' : A * hessPGL (K := K) * A⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ζ₂ * hessPGL (K := K) := by
    simpa [toGL_hessP] using hA₂
  obtain ⟨c, k, j, hA⟩ :=
    exists_scalar_pow_mul_diag_pow_of_normalizer (K := K) hω hω1 hA₁' hA₂'
  let g : SpecialLinearGroup (Fin 3) K := hessP (K := K) ^ k * hessD hω ^ j
  let b : projectiveSL 3 K := proj 3 K g
  have hb_mem : b ∈ hessE9 hω := by
    have hb : b = (proj 3 K (hessP (K := K))) ^ k * (proj 3 K (hessD hω)) ^ j := by
      simp [b, g, map_mul, map_pow]
    rw [hb]
    exact mul_mem (pow_mem hP_mem _) (pow_mem hd_mem _)
  have htoGL : SpecialLinearGroup.toGL g =
      hessPGL (K := K) ^ k * hessDGL hω ^ j := by
    simp [g, map_mul, map_pow, toGL_hessP, toGL_hessD]
  have hconjA : conjAut 3 K A = MulAut.conj b := by
    rw [hA]
    rw [map_mul, conjAut_scalar, one_mul]
    rw [← htoGL]
    change conjAut 3 K (SpecialLinearGroup.toGL g) = MulAut.conj (proj 3 K g)
    exact (KFacts.conj_proj_eq_conjAut (n := 3) (K := K) g).symm
  refine ⟨b, hb_mem, σ, ε, hε, hσω, ?_⟩
  rw [hαgen, hconjA]
  group

theorem fieldAut_mul_dualAut_fixes_hessE9 (σ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1)
    (hσω : σ ω = ω ^ 2 ^ ε) :
    ∀ x ∈ hessE9 hω, (fieldAut 3 K σ * dualAut 3 K ^ ε) x = x := by
  intro x hx
  obtain ⟨i, j, rfl⟩ := (mem_hessE9_iff (hω := hω) x).mp hx
  rw [map_mul, map_pow, map_pow,
    fieldAut_mul_dualAut_fixes_hessD (K := K) hω σ hε hσω,
    fieldAut_mul_dualAut_fixes_hessP (K := K) σ hε]

end Hurwitz

section EveryE9

variable (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)

theorem exists_conjAut_map_eq_hessE9 [CharP K 2] (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    {n : ℕ} (hcard : Nat.card K = 2 ^ n) (h3 : 2 ^ n % 3 = 1) (h9 : 2 ^ n % 9 ≠ 1)
    {B : Subgroup (projectiveSL 3 K)} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) :
    ∃ g : GL (Fin 3) K, B.map (conjAut 3 K g).toMonoidHom = hessE9 hω := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by norm_num))
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hle : 2 ^ n = 1 := by
      have : n = 0 := by omega
      simp [this]
    have hcard' : Nat.card K = 1 := by rw [hcard, hle]
    exact (Finite.one_lt_card (α := K)).ne' hcard'
  have hK : PiField true 2 n K := ⟨Nat.prime_two, hn1, hcard⟩
  have hq : ModThree true (2 ^ n) := h3
  have h9both : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8) := by
    rintro (h | h)
    · exact h9 h
    · have : 2 ^ n % 3 = 2 := by omega
      omega
  have h9dvd : ¬ 9 ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartTwo.Sec15.Proof1513Res3.not_nine_dvd_card_sub_one' hK h9both
  have h3K : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    intro h3zero
    have h1 : (1 : K) = 0 := by
      have h2' : (1 : K) + 1 = 0 := by
        have h2eq : (2 : K) = (1 : K) + 1 := by norm_num
        rwa [h2eq] at h2
      have h3eq : (3 : K) = (1 : K) + 1 + 1 := by norm_num
      rw [h3eq, h2', zero_add] at h3zero
      exact h3zero
    exact one_ne_zero h1
  have h27proj : ¬ 27 ∣ Nat.card (CFSG.PGLModel.projSL 3 K) := by
    rw [Sec4.projSL_eq_projImage (2 ^ n) K]
    exact Sec15.KSL3Two.not_dvd_card_projImage hK hq h9both
  have h27 : ¬ 27 ∣ Nat.card (projectiveSL 3 K) := by
    rwa [Nat.card_congr (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 K).toEquiv]
      at h27proj
  have h9dvdG : 9 ∣ Nat.card (projectiveSL 3 K) := by
    rw [← card_hessE9 (hω := hω) hω1]
    exact Subgroup.card_subgroup_dvd_card (hessE9 hω)
  have hBp : IsPGroup 3 B := hB.isPGroup
  have hEp : IsPGroup 3 (hessE9 hω) := (hessE9_isElemAbelian (hω := hω)).isPGroup
  have hB_sylow : CFSG.DihedralBlueprint.IsSylowIn 3 B ⊤ := by
    refine ⟨le_top, hBp, ?_⟩
    intro Q _ hQp hBQ
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
    have h9Q : 9 ∣ Nat.card Q := by
      have := Subgroup.card_dvd_of_le hBQ
      rwa [hB9] at this
    rw [hk] at h9Q
    have hQdvd : Nat.card Q ∣ Nat.card (projectiveSL 3 K) := Subgroup.card_subgroup_dvd_card Q
    have hkge : 2 ≤ k := by
      have h : 3 ^ 2 ∣ 3 ^ k := by simpa using h9Q
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp h
    have hklt : k < 3 := by
      by_contra hk3
      have h27Q : 27 ∣ Nat.card Q := by
        rw [hk]
        exact pow_dvd_pow 3 (by omega : 3 ≤ k)
      exact h27 (h27Q.trans hQdvd)
    have hQ9 : Nat.card Q = 9 := by
      rw [hk, show k = 2 by omega]
      norm_num
    exact (Subgroup.eq_of_le_of_card_ge hBQ (by rw [hQ9, hB9])).symm
  have hE_sylow : CFSG.DihedralBlueprint.IsSylowIn 3 (hessE9 hω) ⊤ := by
    refine ⟨le_top, hEp, ?_⟩
    intro Q _ hQp hEQ
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
    have h9Q : 9 ∣ Nat.card Q := by
      have := Subgroup.card_dvd_of_le hEQ
      rwa [card_hessE9 (hω := hω) hω1] at this
    rw [hk] at h9Q
    have hQdvd : Nat.card Q ∣ Nat.card (projectiveSL 3 K) := Subgroup.card_subgroup_dvd_card Q
    have hkge : 2 ≤ k := by
      have h : 3 ^ 2 ∣ 3 ^ k := by simpa using h9Q
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp h
    have hklt : k < 3 := by
      by_contra hk3
      have h27Q : 27 ∣ Nat.card Q := by
        rw [hk]
        exact pow_dvd_pow 3 (by omega : 3 ≤ k)
      exact h27 (h27Q.trans hQdvd)
    have hQ9 : Nat.card Q = 9 := by
      rw [hk, show k = 2 by omega]
      norm_num
    exact (Subgroup.eq_of_le_of_card_ge hEQ
      (by rw [hQ9, card_hessE9 (hω := hω) hω1])).symm
  obtain ⟨x, -, hx⟩ := CFSG.DihedralBlueprint.isSylowIn_exists_conjugating_mem 3 Nat.prime_three B
    (hessE9 hω) ⊤ hB_sylow hE_sylow
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  refine ⟨SpecialLinearGroup.toGL g, ?_⟩
  rwa [KFacts.conj_proj_eq_conjAut] at hx

end EveryE9

end MatrixNormalizer

end CFSG.RankThree.PartTwo.KFacts.PSLThreeHessian
